import Ochr.Meaning.Steps.Machine.Zero
import Ochr.Meaning.Steps.Machine.StepSubst
import Ochr.Meaning.Steps.Machine.StepBorrow
import Ochr.Meaning.Steps.Machine.StepPlace
import Ochr.Meaning.Steps.Machine.StepTypes
import Ochr.Meaning.Steps.Machine.StepEval
import Ochr.Meaning.Steps.Machine.StepCall
import Ochr.Meaning.Steps.Machine.StepMatch
import Ochr.Meaning.Steps.Machine.StepJoin
import Ochr.Meaning.Steps.Machine.StepTail
import Ochr.Meaning.Steps.Machine.StepConv

/-!
# The induction over the machine's block, assembled

`machineGrows tb nf`: every function of `Machine.lean`'s mutual block, at every fuel, only extends
the tables from a state with the tables `tb`. The base is `Zero.lean`; the step at `nf + 1` from
the hypothesis at `nf` is `Step*.lean`, one lemma per function.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope

variable {tb : Tab}

theorem retOk_bind {α β : Type} {x : M α} {k : α → M β} {P : β → Prop} (hx : GrowsIn tb x)
    (hk : ∀ a, RetOk tb (k a) P) : RetOk tb (x >>= k) P := by
  refine ⟨fun s f l b s' f' l' hs h => ?_⟩
  rw [runAll_bind] at h
  revert h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h; cases h
  · intro h
    exact (hk a).run s₁ f₁ l₁ b s' f' l' (hs.of_grows (hx s f l a s₁ f₁ l₁ hs e)) h

theorem retOk_pure {α : Type} {a : α} {P : α → Prop} (h : P a) : RetOk tb (pure a : M α) P := by
  refine ⟨fun s f l b s' f' l' _ e => ?_⟩
  cases e; exact h

/-- What `joinCont` returns keeps the tables too: `k` itself, or `k` after the drops of the join. -/
theorem retOk_joinCont (nf : Nat) (ih : MachineGrows tb nf) (mt : Term) (k : Value → Value → M Unit)
    (hk : ∀ r R, GrowsIn tb (k r R)) :
    RetOk tb (Ochr.joinCont (nf + 1) mt k) (fun k' => ∀ r R, GrowsIn tb (k' r R)) := by
  unfold Ochr.joinCont
  dsimp only
  refine retOk_bind (by grows_go ih) fun a => ?_
  split
  · exact retOk_pure hk
  · exact retOk_pure fun r R => by grows_go ih

theorem retOk_joinCont_zero (mt : Term) (k : Value → Value → M Unit) (_ : ∀ r R, GrowsIn tb (k r R)) :
    RetOk tb (Ochr.joinCont 0 mt k) (fun k' => ∀ r R, GrowsIn tb (k' r R)) := by
  refine ⟨fun s f l a s' f' l' _ h => ?_⟩
  cases h

theorem machineGrows_zero : MachineGrows tb 0 where
  substV := zero_substV
  substT := zero_substT
  substEnv := zero_substEnv
  nfSealed := zero_nfSealed
  endBorrow := zero_endBorrow
  lentUnknown := zero_lentUnknown
  repackCheck := zero_repackCheck
  repackAt := zero_repackAt
  bodyReturns := zero_bodyReturns
  endAll := zero_endAll
  obsResult := zero_obsResult
  endTopLoan := zero_endTopLoan
  accessPath := zero_accessPath
  accessInside := zero_accessInside
  openWrite := zero_openWrite
  accessNeutralHead := zero_accessNeutralHead
  readPlace := zero_readPlace
  copyRead := zero_copyRead
  borrowPlace := zero_borrowPlace
  assignPlace := zero_assignPlace
  dropTopBind := zero_dropTopBind
  endLoansOfTopBind := zero_endLoansOfTopBind
  dropValue := zero_dropValue
  endLoansOfTopTemp := zero_endLoansOfTopTemp
  popFrame := zero_popFrame
  placeType? := zero_placeTypeQ
  placeType := zero_placeType
  natPlace := zero_natPlace
  projIn := zero_projIn
  projMatch := zero_projMatch
  depFieldType := zero_depFieldType
  fieldDeclType := zero_fieldDeclType
  packedErr := zero_packedErr
  convVal := zero_convVal
  valType? := zero_valTypeQ
  valType := zero_valType
  sealedType? := zero_sealedTypeQ
  fieldTele := zero_fieldTele
  fieldTypes := zero_fieldTypes
  fieldTypesOf := zero_fieldTypesOf
  fieldsGeneric := zero_fieldsGeneric
  fieldTypeAt := zero_fieldTypeAt
  indValType? := zero_indValTypeQ
  bindDataFields := zero_bindDataFields
  piSort := zero_piSort
  evalType := zero_evalType
  capture := zero_capture
  conv := zero_conv
  convList := zero_convList
  convTList := zero_convTList
  convPi := zero_convPi
  convT := zero_convT
  convFn := zero_convFn
  convFnRun := zero_convFnRun
  mkEqM := zero_mkEqM
  rewriteGoal := zero_rewriteGoal
  expectTy := zero_expectTy
  eval := zero_eval
  evalAt := zero_evalAt
  evalCore := zero_evalCore
  unknownLent := zero_unknownLent
  lentProofAssign := zero_lentProofAssign
  lentLeafCheck := zero_lentLeafCheck
  evalTInd := zero_evalTInd
  evalParams := zero_evalParams
  checkParams := zero_checkParams
  evalCtor := zero_evalCtor
  stmtCallee := zero_stmtCallee
  evalCall := zero_evalCall
  argHint := zero_argHint
  funType? := zero_funTypeQ
  funType := zero_funType
  callType := zero_callType
  declCallType := zero_declCallType
  forceHint := zero_forceHint
  paramTypes := zero_paramTypes
  bindTy? := zero_bindTyQ
  endBorrowArgs := zero_endBorrowArgs
  runBody := zero_runBody
  runBodyCore := zero_runBodyCore
  callFn := zero_callFn
  closeCall := zero_closeCall
  refine := zero_refine
  evalMatch := zero_evalMatch
  natScrutinee := zero_natScrutinee
  generalizeNeutral := zero_generalizeNeutral
  sealedResultType? := zero_sealedResultTypeQ
  renormAll := zero_renormAll
  renormV := zero_renormV
  renormT := zero_renormT
  splitThenClose := zero_splitThenClose
  splitArmsThenClose := zero_splitArmsThenClose
  ctorRefinement := zero_ctorRefinement
  scrutType := zero_scrutType
  evalMatchByType := zero_evalMatchByType
  evalMatchInd := zero_evalMatchInd
  etaInPlace := zero_etaInPlace
  etaPlace := zero_etaPlace
  movedPlace := zero_movedPlace
  staticJoin := zero_staticJoin
  joinDrop := zero_joinDrop
  joinCont := zero_joinCont
  joinEnds := zero_joinEnds
  blockEntry := zero_blockEntry
  entryAccess := zero_entryAccess
  dropAtJoin := zero_dropAtJoin
  blockCaptures := zero_blockCaptures
  closeBlock := zero_closeBlock
  observe := zero_observe
  idType := zero_idType
  stuckScrutinee := zero_stuckScrutinee
  findSplit := zero_findSplit
  generalizeFound := zero_generalizeFound
  splitTarget := zero_splitTarget
  checkTail := zero_checkTail
  checkTailAt := zero_checkTailAt
  checkFix := zero_checkFix
  joinContRet := retOk_joinCont_zero

theorem machineGrows_succ (nf : Nat) (ih : MachineGrows tb nf) : MachineGrows tb (nf + 1) where
  substV := step_substV ih
  substT := step_substT ih
  substEnv := step_substEnv ih
  nfSealed := step_nfSealed ih
  endBorrow := step_endBorrow ih
  lentUnknown := step_lentUnknown ih
  repackCheck := step_repackCheck ih
  repackAt := step_repackAt ih
  bodyReturns := step_bodyReturns ih
  endAll := step_endAll ih
  obsResult := step_obsResult ih
  endTopLoan := step_endTopLoan ih
  accessPath := step_accessPath ih
  accessInside := step_accessInside ih
  openWrite := step_openWrite ih
  accessNeutralHead := step_accessNeutralHead ih
  readPlace := step_readPlace ih
  copyRead := step_copyRead ih
  borrowPlace := step_borrowPlace ih
  assignPlace := step_assignPlace ih
  dropTopBind := step_dropTopBind ih
  endLoansOfTopBind := step_endLoansOfTopBind ih
  dropValue := step_dropValue ih
  endLoansOfTopTemp := step_endLoansOfTopTemp ih
  popFrame := step_popFrame ih
  placeType? := step_placeTypeQ ih
  placeType := step_placeType ih
  natPlace := step_natPlace ih
  projIn := step_projIn ih
  projMatch := step_projMatch ih
  depFieldType := step_depFieldType ih
  fieldDeclType := step_fieldDeclType ih
  packedErr := step_packedErr ih
  convVal := step_convVal ih
  valType? := step_valTypeQ ih
  valType := step_valType ih
  sealedType? := step_sealedTypeQ ih
  fieldTele := step_fieldTele ih
  fieldTypes := step_fieldTypes ih
  fieldTypesOf := step_fieldTypesOf ih
  fieldsGeneric := step_fieldsGeneric ih
  fieldTypeAt := step_fieldTypeAt ih
  indValType? := step_indValTypeQ ih
  bindDataFields := step_bindDataFields ih
  piSort := step_piSort ih
  evalType := step_evalType ih
  capture := step_capture ih
  conv := step_conv ih
  convList := step_convList ih
  convTList := step_convTList ih
  convPi := step_convPi ih
  convT := step_convT ih
  convFn := step_convFn ih
  convFnRun := step_convFnRun ih
  mkEqM := step_mkEqM ih
  rewriteGoal := step_rewriteGoal ih
  expectTy := step_expectTy ih
  eval := step_eval ih
  evalAt := step_evalAt ih
  evalCore := step_evalCore ih
  unknownLent := step_unknownLent ih
  lentProofAssign := step_lentProofAssign ih
  lentLeafCheck := step_lentLeafCheck ih
  evalTInd := step_evalTInd ih
  evalParams := step_evalParams ih
  checkParams := step_checkParams ih
  evalCtor := step_evalCtor ih
  stmtCallee := step_stmtCallee ih
  evalCall := step_evalCall ih
  argHint := step_argHint ih
  funType? := step_funTypeQ ih
  funType := step_funType ih
  callType := step_callType ih
  declCallType := step_declCallType ih
  forceHint := step_forceHint ih
  paramTypes := step_paramTypes ih
  bindTy? := step_bindTyQ ih
  endBorrowArgs := step_endBorrowArgs ih
  runBody := step_runBody ih
  runBodyCore := step_runBodyCore ih
  callFn := step_callFn ih
  closeCall := step_closeCall ih
  refine := step_refine ih
  evalMatch := step_evalMatch ih
  natScrutinee := step_natScrutinee ih
  generalizeNeutral := step_generalizeNeutral ih
  sealedResultType? := step_sealedResultTypeQ ih
  renormAll := step_renormAll ih
  renormV := step_renormV ih
  renormT := step_renormT ih
  splitThenClose := step_splitThenClose ih
  splitArmsThenClose := step_splitArmsThenClose ih
  ctorRefinement := step_ctorRefinement ih
  scrutType := step_scrutType ih
  evalMatchByType := step_evalMatchByType ih
  evalMatchInd := step_evalMatchInd ih
  etaInPlace := step_etaInPlace ih
  etaPlace := step_etaPlace ih
  movedPlace := step_movedPlace ih
  staticJoin := step_staticJoin ih
  joinDrop := step_joinDrop ih
  joinCont := step_joinCont ih
  joinEnds := step_joinEnds ih
  blockEntry := step_blockEntry ih
  entryAccess := step_entryAccess ih
  dropAtJoin := step_dropAtJoin ih
  blockCaptures := step_blockCaptures ih
  closeBlock := step_closeBlock ih
  observe := step_observe ih
  idType := step_idType ih
  stuckScrutinee := step_stuckScrutinee ih
  findSplit := step_findSplit ih
  generalizeFound := step_generalizeFound ih
  splitTarget := step_splitTarget ih
  checkTail := step_checkTail ih
  checkTailAt := step_checkTailAt ih
  checkFix := step_checkFix ih
  joinContRet := retOk_joinCont nf ih

/-- **Every function of the machine's mutual block only extends the tables**, at every fuel, from
a state with any tables. -/
theorem machineGrows : ∀ nf, MachineGrows tb nf
  | 0 => machineGrows_zero
  | nf + 1 => machineGrows_succ nf (machineGrows nf)

end Ochr.Meaning.Steps.Machine

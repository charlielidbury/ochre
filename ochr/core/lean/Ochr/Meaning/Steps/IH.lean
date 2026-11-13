import Ochr.Meaning.Steps.Statements

/-!
# The bundled induction hypothesis (milestone 3)

`StepsIH K ρ φ fuel`: every step statement at `fuel`. An area file proves its statements at
`fuel + 1` from the hypothesis at `fuel` **at every assignment and future** (`∀ ρ φ, StepsIH K ρ φ
fuel`); `Steps/Knot.lean` closes the induction. There is no knot field: a state is read through
`K.M = codeMeaning K` (docs/31 D18).
-/

namespace Ochr.Meaning.Steps

structure StepsIH (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop where
  endBorrow_step : endBorrow_step_stmt K ρ φ fuel
  access_step : access_step_stmt K ρ φ fuel
  readPlace_step : readPlace_step_stmt K ρ φ fuel
  borrowPlace_step : borrowPlace_step_stmt K ρ φ fuel
  assignPlace_step : assignPlace_step_stmt K ρ φ fuel
  dropTopBind_step : dropTopBind_step_stmt K ρ φ fuel
  popFrame_step : popFrame_step_stmt K ρ φ fuel
  substV_loan_step : substV_loan_step_stmt K ρ φ fuel
  substV_abs_step : substV_abs_step_stmt K ρ φ fuel
  substEnv_loan_step : substEnv_loan_step_stmt K ρ φ fuel
  substEnv_abs_step : substEnv_abs_step_stmt K ρ φ fuel
  nfSealed_step : nfSealed_step_stmt K ρ φ fuel
  canonNeutral_step : canonNeutral_step_stmt K ρ φ fuel
  renormAll_step : renormAll_step_stmt K ρ φ fuel
  refine_step : refine_step_stmt K ρ φ fuel
  mkEqM_step : mkEqM_step_stmt K ρ φ fuel
  conv_sound : conv_sound_stmt K ρ φ fuel
  convPi_sound : convPi_sound_stmt K ρ φ fuel
  convFn_sound : convFn_sound_stmt K ρ φ fuel
  rewriteGoal_step : rewriteGoal_step_stmt K ρ φ fuel
  type_futureFree : type_futureFree_stmt K ρ φ fuel
  callFn_step : callFn_step_stmt K ρ φ fuel
  runBody_step : runBody_step_stmt K ρ φ fuel
  closeCall_step : closeCall_step_stmt K ρ φ fuel
  callType_step : callType_step_stmt K ρ φ fuel
  recCheck_sound : recCheck_sound_stmt K ρ φ fuel
  evalMatch_step : evalMatch_step_stmt K ρ φ fuel
  evalMatchInd_step : evalMatchInd_step_stmt K ρ φ fuel
  evalMatchByType_step : evalMatchByType_step_stmt K ρ φ fuel
  split_coverage : split_coverage_stmt K ρ φ fuel
  generalizeNeutral_step : generalizeNeutral_step_stmt K ρ φ fuel
  closeBlock_step : closeBlock_step_stmt K ρ φ fuel
  exitWorld_step : exitWorld_step_stmt K ρ φ fuel
  observe_step : observe_step_stmt K ρ φ fuel
  footprint_coverage : footprint_coverage_stmt K ρ φ fuel
  idType_step : idType_step_stmt K ρ φ fuel
  owners_sound : owners_sound_stmt K ρ φ fuel
  evalType_step : evalType_step_stmt K ρ φ fuel
  piSort_aligned : piSort_aligned_stmt K ρ φ fuel
  capture_step : capture_step_stmt K ρ φ fuel
  evalCtor_step : evalCtor_step_stmt K ρ φ fuel
  evalTInd_step : evalTInd_step_stmt K ρ φ fuel
  fieldTypesOf_step : fieldTypesOf_step_stmt K ρ φ fuel
  repackCheck_sound : repackCheck_sound_stmt K ρ φ fuel
  bodyReturns_sound : bodyReturns_sound_stmt K ρ φ fuel
  valType_sound : valType_sound_stmt K ρ φ fuel
  borrow_wf : borrow_wf_stmt K ρ φ fuel
  end_wf : end_wf_stmt K ρ φ fuel
  assign_wf : assign_wf_stmt K ρ φ fuel
  close_wf : close_wf_stmt K ρ φ fuel
  capture_wf : capture_wf_stmt K ρ φ fuel
  eval_wf6 : eval_wf6_stmt K ρ φ fuel
  eval_wf78 : eval_wf78_stmt K ρ φ fuel
  types_holeFree : types_holeFree_stmt K ρ φ fuel
  evalCore_step : evalCore_step_stmt K ρ φ fuel
  eval_step : eval_step_stmt K ρ φ fuel
  letIn_step : letIn_step_stmt K ρ φ fuel
  eq_step : eq_step_stmt K ρ φ fuel
  J_step : J_step_stmt K ρ φ fuel
  proof_step : proof_step_stmt K ρ φ fuel
  etaUnit_step : etaUnit_step_stmt K ρ φ fuel
  generic_good : generic_good_stmt K ρ φ fuel
  checkTail_step : checkTail_step_stmt K ρ φ fuel
  checkFix_sound : checkFix_sound_stmt K ρ φ fuel
  checkConst_sound : checkConst_sound_stmt K ρ φ fuel
  checkInd_sound : checkInd_sound_stmt K ρ φ fuel
  scopeOf_sstate : scopeOf_sstate_stmt K ρ φ fuel
  flags_aligned : flags_aligned_stmt K ρ φ fuel
  placeDecl_aligned : placeDecl_aligned_stmt K ρ φ fuel
  declOf_aligned : declOf_aligned_stmt K ρ φ fuel
  copy_aligned : copy_aligned_stmt K ρ φ fuel
  piSort_aligned' : piSort_aligned'_stmt K ρ φ fuel
  joinMoves_aligned : joinMoves_aligned_stmt K ρ φ fuel
  rePointed_aligned : rePointed_aligned_stmt K ρ φ fuel
  typeDecl_aligned : typeDecl_aligned_stmt K ρ φ fuel

end Ochr.Meaning.Steps

import Ochr.Meaning.Steps.Borrow
import Ochr.Meaning.Steps.Subst
import Ochr.Meaning.Steps.Eq
import Ochr.Meaning.Steps.Call
import Ochr.Meaning.Steps.Match
import Ochr.Meaning.Steps.Obs
import Ochr.Meaning.Steps.Types
import Ochr.Meaning.Steps.WF
import Ochr.Meaning.Steps.Eval
import Ochr.Meaning.Steps.Tail
import Ochr.Meaning.Steps.Decisions

/-!
# The knot of the step lemmas (milestone 3): induction on fuel

`stepsIH`: every step statement holds at every fuel, assignment and future (no knot hypothesis:
docs/31 D18). The successor case is the area files' theorems applied to the hypothesis at `fuel`,
which they get at every assignment and future. The base case: a checker function at
fuel `0` is `exhausted`, so every `Runs … 0 …` hypothesis is false and the fuel-indexed
statements hold vacuously; the statements without a fuel-indexed run must be proved outright
(`stepsIH_zero`).
-/

namespace Ochr.Meaning.Steps

section
variable (K : RunCtx)

/-- The base of the induction. -/
theorem stepsIH_zero (ρ : Assignment) (φ : Future) : StepsIH K ρ φ 0 := by
  sorry

/-- Every step statement, at every fuel, assignment and future. -/
theorem stepsIH : ∀ (fuel : Nat) (ρ : Assignment) (φ : Future), StepsIH K ρ φ fuel
  | 0, ρ, φ => stepsIH_zero K ρ φ
  | fuel + 1, ρ, φ =>
    let ih := stepsIH fuel
    { endBorrow_step := endBorrow_step K ρ φ fuel ih
      access_step := access_step K ρ φ fuel ih
      readPlace_step := readPlace_step K ρ φ fuel ih
      borrowPlace_step := borrowPlace_step K ρ φ fuel ih
      assignPlace_step := assignPlace_step K ρ φ fuel ih
      dropTopBind_step := dropTopBind_step K ρ φ fuel ih
      popFrame_step := popFrame_step K ρ φ fuel ih
      substV_loan_step := substV_loan_step K ρ φ fuel ih
      substV_abs_step := substV_abs_step K ρ φ fuel ih
      substEnv_loan_step := substEnv_loan_step K ρ φ fuel ih
      substEnv_abs_step := substEnv_abs_step K ρ φ fuel ih
      nfSealed_step := nfSealed_step K ρ φ fuel ih
      canonNeutral_step := canonNeutral_step K ρ φ fuel ih
      renormAll_step := renormAll_step K ρ φ fuel ih
      refine_step := refine_step K ρ φ fuel ih
      mkEqM_step := mkEqM_step K ρ φ fuel ih
      conv_sound := conv_sound K ρ φ fuel ih
      convPi_sound := convPi_sound K ρ φ fuel ih
      convFn_sound := convFn_sound K ρ φ fuel ih
      rewriteGoal_step := rewriteGoal_step K ρ φ fuel ih
      type_futureFree := type_futureFree K ρ φ fuel ih
      callFn_step := callFn_step K ρ φ fuel ih
      runBody_step := runBody_step K ρ φ fuel ih
      closeCall_step := closeCall_step K ρ φ fuel ih
      callType_step := callType_step K ρ φ fuel ih
      recCheck_sound := recCheck_sound K ρ φ fuel ih
      evalMatch_step := evalMatch_step K ρ φ fuel ih
      evalMatchInd_step := evalMatchInd_step K ρ φ fuel ih
      evalMatchByType_step := evalMatchByType_step K ρ φ fuel ih
      split_coverage := split_coverage K ρ φ fuel ih
      generalizeNeutral_step := generalizeNeutral_step K ρ φ fuel ih
      closeBlock_step := closeBlock_step K ρ φ fuel ih
      exitWorld_step := exitWorld_step K ρ φ fuel ih
      observe_step := observe_step K ρ φ fuel ih
      footprint_coverage := footprint_coverage K ρ φ fuel ih
      idType_step := idType_step K ρ φ fuel ih
      owners_sound := owners_sound K ρ φ fuel ih
      evalType_step := evalType_step K ρ φ fuel ih
      piSort_aligned := piSort_aligned K ρ φ fuel ih
      capture_step := capture_step K ρ φ fuel ih
      evalCtor_step := evalCtor_step K ρ φ fuel ih
      evalTInd_step := evalTInd_step K ρ φ fuel ih
      fieldTypesOf_step := fieldTypesOf_step K ρ φ fuel ih
      repackCheck_sound := repackCheck_sound K ρ φ fuel ih
      bodyReturns_sound := bodyReturns_sound K ρ φ fuel ih
      valType_sound := valType_sound K ρ φ fuel ih
      borrow_wf := borrow_wf K ρ φ fuel ih
      end_wf := end_wf K ρ φ fuel ih
      assign_wf := assign_wf K ρ φ fuel ih
      close_wf := close_wf K ρ φ fuel ih
      capture_wf := capture_wf K ρ φ fuel ih
      eval_wf6 := eval_wf6 K ρ φ fuel ih
      eval_wf78 := eval_wf78 K ρ φ fuel ih
      types_holeFree := types_holeFree K ρ φ fuel ih
      evalCore_step := evalCore_step K ρ φ fuel ih
      letIn_step := letIn_step K ρ φ fuel ih
      eq_step := eq_step K ρ φ fuel ih
      J_step := J_step K ρ φ fuel ih
      proof_step := proof_step K ρ φ fuel ih
      etaUnit_step := etaUnit_step K ρ φ fuel ih
      generic_good := generic_good K ρ φ fuel ih
      checkTail_step := checkTail_step K ρ φ fuel ih
      checkFix_sound := checkFix_sound K ρ φ fuel ih
      checkConst_sound := checkConst_sound K ρ φ fuel ih
      checkInd_sound := checkInd_sound K ρ φ fuel ih
      scopeOf_sstate := scopeOf_sstate K ρ φ fuel ih
      flags_aligned := flags_aligned K ρ φ fuel ih
      placeDecl_aligned := placeDecl_aligned K ρ φ fuel ih
      declOf_aligned := declOf_aligned K ρ φ fuel ih
      copy_aligned := copy_aligned K ρ φ fuel ih
      piSort_aligned' := piSort_aligned' K ρ φ fuel ih
      joinMoves_aligned := joinMoves_aligned K ρ φ fuel ih
      rePointed_aligned := rePointed_aligned K ρ φ fuel ih
    }

end

end Ochr.Meaning.Steps

import Och.Soundness
import Och.TypedNbE
#print axioms Och.Soundness.soundness
#print axioms Och.Soundness.typeCheck_sound
#print axioms Och.Soundness.concEval_equiv_closed
#print axioms Och.Soundness.concEval_preservation
#print axioms Och.Soundness.eval_quote_equiv_closed
#print axioms NbE.R_depth_lift
#print axioms NbE.R_quote_equiv
#print axioms NbE.vapp_realises
#print axioms NbE.eval_realises
#print axioms NbE.tyCheck_sound_open
#print axioms NbE.tyInfer_sound_open
#print axioms NbE.quote_depth_shift
#print axioms NbE.Equiv_c.shift
#print axioms NbE.Equiv_c.trans
#print axioms NbE.Equiv_c.of_Equiv
#print axioms NbE.substEnv_shift_comm
#print axioms NbE.Equiv_c.subst_resp
#print axioms NbE.quoteClosure_realises

-- Pass 3 phase 1+2 substrate lemmas (saturated RC).
-- These should be axiom-clean (no sorryAx) because Phase 2's
-- saturation refactor turned implies_* into direct projections.
#print axioms NbE.RC.mono
#print axioms NbE.RC.fullyQuotable
#print axioms NbE.RC.quote_witness
#print axioms NbE.RC.implies_fullyQuotable
#print axioms NbE.RC.implies_quote_terminates
#print axioms NbE.RC.lam_intro
#print axioms NbE.RC.iota_intro
#print axioms NbE.RC.fix_intro
#print axioms NbE.RC.lam_elim
#print axioms NbE.RC.iota_elim
#print axioms NbE.RC.fix_elim
#print axioms NbE.RC.type_top
#print axioms NbE.RC.neutral_top

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

-- Pass 4 sorried lemmas — these still depend on sorryAx until
-- the FL body and subtype_closed are closed.
#print axioms NbE.RC.subtype_closed_aux
#print axioms NbE.RC.subtype_closed
-- Pass 7: body-substitution lemma (basic, single substituent).
-- Sorried; consolidates the `lam`/`iota_struct` cases of
-- `subtype_closed_aux`. Closing it makes those two axiom-clean.
#print axioms NbE.SubV_subst_neutral_to_value
-- Pass 8: pair-substitution generalisation (different
-- substituents on each side). Sorried; consolidates the
-- `fix_struct` case of `subtype_closed_aux`. Closing it makes
-- `fix_struct` axiom-clean.
#print axioms NbE.SubV_subst_pair
-- Pass 5: FL signature reformulated to take an open environment.
-- The closed form is recoverable by specialising at empty Γ/ρ.
#print axioms NbE.typed_nbe_fundamental_open
-- Pass 5: typed env realisation lemmas.
#print axioms NbE.RC_env.nil
#print axioms NbE.RC_env.cons
-- Pass 10: step-index downward monotonicity for RC_env.
#print axioms NbE.RC_env.mono
-- Pass 6: typed-everything `SubTV` substrate. These are
-- axiom-clean (no sorryAx) — they're proven via RC's
-- saturation projections + RC.subtype_closed.
-- `SubTV.of_SubV` transitively depends on RC.subtype_closed
-- (which has 8 inline sorries on hard cases), but the
-- substrate constructors themselves are sorry-free.
#print axioms NbE.SubTV.refl
#print axioms NbE.SubTV.trans
#print axioms NbE.SubTV.bot_L
#print axioms NbE.SubTV.top
#print axioms NbE.SubTV.to_neutral
#print axioms NbE.SubTV.of_SubV
#print axioms NbE.SubTV.coerce

-- Pass 13: identity-on-closed substitution, well-formedness
-- predicate, and envSubstLvl list-operation commutation lemmas.
-- These are sorry-free infrastructure for the eval-commutation
-- proof that pass 14 will attempt.
#print axioms NbE.Val.substLvl_of_levelsBelow
#print axioms NbE.Neutral.substLvl_of_levelsBelow
#print axioms NbE.Closure.substLvl_of_levelsBelow
#print axioms NbE.Closure.envSubstLvl_of_levelsBelow
#print axioms NbE.Closure.envSubstLvl_cons
#print axioms NbE.Closure.envSubstLvl_cons_inv
#print axioms NbE.Closure.envSubstLvl_length
#print axioms NbE.Closure.envSubstLvl_getElem?
#print axioms NbE.Closure.envSubstLvl_take
#print axioms NbE.Closure.envWellFormed_take
#print axioms NbE.Closure.envWellFormed_getElem?

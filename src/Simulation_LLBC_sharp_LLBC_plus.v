From stdpp Require Import pmap.
Require Import base SimulationUtils PathToSubtree lang.
Require Import Symbolic_states Symbolic_relations LLBC_plus LLBC_sharp Simulation_LLBC_plus.

Local Open Scope llbc_sharp_scope.
Local Open Scope llbc_plus_scope.

Lemma simulation_LLBC_sharp_LLBC_plus n s :
  forward_simulation eq leq_branching (LLBC_sharp.eval_stmt s) (LLBC_plus.eval_stmt n s).
Proof.
  intros Sr Br eval_Sr ? ->. revert s Sr Br eval_Sr. induction n as [ | n IHn]; intros.
  - execution_step. { apply LLBC_plus.E_Step_Zero. }
    intros r. unfold branching_state. simpl_map. constructor.
  - induction eval_Sr.
    (* Case [LLBC_sharp.E_Nop] *)
    + execution_step. { constructor. } reflexivity.
    (* Case [LLBC_sharp.E_Panic] *)
    + execution_step. { constructor. } reflexivity.
    (* Case [LLBC_sharp.E_Break] *)
    + execution_step. { constructor. } reflexivity.
    (* Case [LLBC_sharp.E_Continue] *)
    + execution_step. { constructor. } reflexivity.

    (* Case [LLBC_sharp.E_Seq_Unit_Propagate] *)
    + destruct IHeval_Sr as (Bl & ? & ?).
      execution_step. { eapply LLBC_plus.E_Seq_Propagate; eauto with spath. }
      assumption.
    (* Case [LLBC_sharp.E_Seq_Unit_Propagate] *)
    + destruct IHeval_Sr1 as (B1_l & Hleq_B1 & ?).
      destruct IHeval_Sr2 as (B2_m & Hleq_B2 & ?).
      eapply lookup_token_cases in Hleq_B1; [ | exact H_unit].
      destruct Hleq_B1 as [(? & ?) | (S1_l & ? & Hleq_S1 & ?)].
      * execution_step. { apply LLBC_plus.E_Seq_Propagate; eassumption. }
        etransitivity; eassumption.
      * eapply stmt_preserves_LLBC_plus_rel in Hleq_S1; [ | eassumption].
        destruct Hleq_S1 as (B2_l & ? & ?).
        execution_join_state.
        { eapply LLBC_plus.E_Seq_Unit_Propagate; eassumption. }
        { transitivity B2_m; assumption. }
        { etransitivity; eauto with spath. }

    (* Case [LLBC_sharp.E_Assign] *)
    + execution_step. { econstructor; eassumption. } reflexivity.
    (* Case [LLBC_sharp.E_IfThenElse_T] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus.E_IfThenElse_T; eassumption. } assumption.
    (* Case [LLBC_sharp.E_IfThenElse_F] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus.E_IfThenElse_F; eassumption. } assumption.

    (* Case [LLBC_sharp.E_IfThenElse_Symbolic] *)
    + destruct IHeval_Sr1 as (B_if & ? & ?). destruct IHeval_Sr2 as (B_else & ? & ?).
      execution_join_state.
      { eapply LLBC_plus.E_IfThenElse_Symbolic; eassumption. }
      { assumption. }
      { assumption. }
    (* Case [LLBC_sharp.E_Reorg] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus.E_Reorg; eassumption. } assumption.
    (* Case [LLBC_sharp.E_Loop_Stop] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus.E_Loop_Stop; eauto with spath. } auto with spath.
    (* Case [LLBC_sharp.E_Loop_Continue] *)
    + destruct IHeval_Sr1 as (B1_l & leq_B1 & ?). clear IHeval_Sr2.
      destruct (lookup_token_cases _ _ _ rContinue leq_B1 Hcontinue)
        as [(? & ?) | (S1_l & ? & leq_S1 & leq_B1')].
      * execution_step. { apply LLBC_plus.E_Loop_Stop; eauto with spath. }
        etransitivity; eauto with spath.
      * eapply LLBC_sharp.Consequence_Precondition in eval_Sr2; [ | exact leq_S1].
        apply IHn in eval_Sr2. destruct eval_Sr2 as (B2_l & ? & ?).
        execution_join_state.
        { eapply LLBC_plus.E_Loop_Continue; eauto with spath. }
        { etransitivity; eauto with spath. }
        { assumption. }

    (* Case [LLBC_sharp.E_Loop_Invariant]: *)
    + destruct IHeval_Sr as (B1 & leq_B1 & eval_to_B1).
      edestruct (lookup_token_cases _ _ _ rContinue leq_B1 inv_preservation)
        as [(? & ?) | (S1 & ? & leq_S1 & leq_B1')].
      * execution_step. { apply LLBC_plus.E_Loop_Stop; eauto with spath. }
        apply leq_end_loop. assumption.
      * assert (S1 |-# LOOP {{ body }} ~> (end_loop (delete rContinue Binv))) as eval_S1.
        { eapply LLBC_sharp.Consequence_Precondition; [exact leq_S1 | ].
          apply LLBC_sharp.E_Loop_Invariant; assumption. }
        apply IHn in eval_S1. destruct eval_S1 as (B2 & leq_B2 & eval_to_B2).
        execution_join_state.
        { eapply LLBC_plus.E_Loop_Continue; eauto with spath. }
        { auto with spath. }
        { assumption. }

    (* Case [LLBC_sharp.Consequence_Precondition]: *)
    + destruct IHeval_Sr as (? & ? & ?).
      eapply stmt_preserves_LLBC_plus_rel in Hweaken; [ | eassumption].
      destruct Hweaken as (? & ? & ?).
      execution_step. { eassumption. } etransitivity; eassumption.
    (* Case [LLBC_sharp.Consequence_Postcondition]: *)
    + destruct IHeval_Sr as (B & Hleq_B & ?).
      execution_step. { eassumption. } transitivity Bl; assumption.
Qed.

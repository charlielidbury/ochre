(** * Mechanized_LLBC.LLBC_sharp_execution : Execution of a LLBC+ program. *)
From Stdlib Require Import List.
Import ListNotations.
From stdpp Require Import decidable pmap.
Require Import base PathToSubtree SimulationUtils lang.
Require Import LLBC_sharp_states LLBC_sharp_relations LLBC_sharp_semantics.

(** Utilities to execute programs. *)
Definition decide_not_contains_outer_loan v :=
  match v with
  | loan^m(_, l) => false
  | _ => true
  end.

(* TODO: move in PathToSubtree.v *)
Lemma valid_vpath_no_children v p (valid_p : valid_vpath v p) (H : children v = []) : p = [].
Proof.
  induction valid_p as [ | ? ? ? ? G].
  - reflexivity.
  - rewrite H, nth_error_nil in G. inversion G.
Qed.

(* For the moment, the type of values is so restricted that a value contains an outer loan if and
 * only if it is a mutable loan. *)
Lemma decide_not_contains_outer_loan_correct v :
  is_true (decide_not_contains_outer_loan v) -> not_contains_outer_loan v.
Proof.
  intros no_outer_loan [ | ] _ H.
  - destruct v; inversion H. discriminate.
  - destruct v; rewrite vget_cons, ?nth_error_nil, ?vget_bot in H; inversion H.
    exists []. split.
    * eexists _, _. reflexivity.
    * constructor.
Qed.

Instance decidable_not_value_contains P `(P_dec : forall n, Decision (P n)) v :
  Decision (not_value_contains P v).
Proof.
  induction v; eauto using decidable_not_value_contains_zeroary, decidable_not_value_contains_unary.
Defined.

Instance decidable_is_loan v : Decision (is_loan v).
Proof. destruct v; first [left; easy | right; easy]. Defined.

Instance decidable_is_borrow v : Decision (is_borrow v).
Proof. destruct v; first [left; easy | right; easy]. Defined.

Instance LLBC_sharp_val_EqDec : EqDecision LLBC_sharp_nodes.
Proof. intros ? ?. unfold Decision. repeat decide equality. Defined.

Instance decide_is_fresh l S : Decision (is_fresh l S).
Proof. apply decidable_not_state_contains. unfold is_loan_id. solve_decision. Defined.

(* Note: an alternative to using tactics is to define functions, and prove their correction. *)
(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
Ltac eval_var :=
  split; [eexists; split; [reflexivity | constructor] | ].

Ltac remove_abstraction i :=
  lazymatch goal with
  | |- ?leq_star ?S _ =>
      erewrite<- (add_remove_abstraction i _ S) by reflexivity;
      rewrite ?remove_add_abstraction_ne by congruence
  end.

Ltac remove_anon a :=
  lazymatch goal with
  | |- ?leq_star ?S _ => erewrite<- (add_anon_remove_anon S a) by reflexivity
  end.

Lemma prove_leq_symbolic Sl Sm Sr :
  leq_state_base^* Sl Sm -> leq_symbolic Sm Sr -> leq_symbolic Sl Sr.
Proof.
  intros H (? & G & ?).
  pose proof leq_equiv_states_commute as Hsim.
  apply sim_leq_equiv in Hsim. specialize (Hsim _ _ G _ H).
  edestruct Hsim as (Sl' & ? & ?).
  exists Sl'. split; [assumption | ]. etransitivity; eassumption.
Qed.

(* These two lemmas are used to show to limited cases of store_compatible_types.
 * Ideally, to be as general as possible when showing
 * [store_compatible_types S (acc, p) v], we should strip the last elements of p one by one,
 * and for each encountered borrow, prove that the type is preserved. *)
Lemma store_compatible_types_nil S acc v : store_compatible_types S (acc, []) v.
Proof. intros q prefix_q_nil%not_strict_prefix_nil. contradiction. Qed.

Lemma store_compatible_types_borrow S acc v ty :
  is_of_type ty v -> is_of_type ty (S.[(acc, [0])]) ->
  store_compatible_types S (acc, [0]) v.
Proof.
  intros ? ? q. replace (acc, [0]) with ((acc, []) +++ [0]) by reflexivity.
  rewrite strict_prefix_app_last. intros ->%prefix_nil _.
  exists ty. split; assumption.
Qed.

(* TODO: rename LLBC_plus_E_Seq_Unit_Propagate to LLBC_plus_E_Seq_Unit_Propagate. *)
Lemma eval_seq_unit n S0 S1 B2 stmt_l stmt_r
  (eval_stmt_l : S0 |-{stmt} stmt_l ~>{1 + n} {[rUnit := S1]})
  (eval_stmt_r : S1 |-{stmt} stmt_r ~>{1 + n} B2) :
  S0 |-{stmt} (Seq stmt_l stmt_r) ~>{1 + n} B2.
Proof.
  eapply LLBC_plus_E_Seq_Unit_Propagate.
  - exact eval_stmt_l.
  - reflexivity.
  - exact eval_stmt_r.
  - (* TODO: lemma? *)
    intros r. unfold branching_state. rewrite delete_singleton, lookup_empty.
    destruct (lookup _ _); constructor.
Qed.

Lemma is_join_singletons r S0 S1 Sjoin :
  leq_symbolic S0 Sjoin -> leq_symbolic S1 Sjoin ->
  is_join {[r := S0]} {[r := S1]} {[r := Sjoin]}.
Proof.
  intros ? ? r'. destruct (decide (r' = r)) as [-> | ].
  - simpl_map. constructor; assumption.
  - unfold branching_state. simpl_map. constructor.
Qed.

Local Open Scope option_monad_scope.
(** The program we execute is:
<<
fn f(x : i32, y : i32) {
   let z;
   if x <= y {
       z = &mut x;
   }
   else {
       z = &mut y;
   }
   *z += 1;
   x += 2;
}
>>
 *)
Notation x := 1%positive.
Notation y := 2%positive.
Notation z := 3%positive.
Notation cond := 4%positive.

(* TODO: solve scope issues. *)
Close Scope stdpp_scope.

(** Note that we have to introduce a temporary variable [cond] to store the result of the comparison. *)
Definition f :=
  ASSIGN (cond, []) <- BinaryOp BLe (Copy (x, [])) (Copy (y, []));;
  IF Copy (cond, []) {{
    ASSIGN (z, []) <- &mut (x, [])
  }}
  ELSE {{
    ASSIGN (z, []) <- &mut (y, [])
  }};;
  ASSIGN (z, [Deref]) <- BinaryOp BAdd (Copy (z, [Deref])) (Const (IntConst 1));;
  ASSIGN (x, []) <- BinaryOp BAdd (Copy (x, [])) (Const (IntConst 2))
.

Open Scope stdpp.
(** We execute the function [f] on the most general state. The arguments << x >> and << y >> are initialized as symbolic values, while the local variables are uninitialized. *)
Definition init_state := {|
  vars := {[x := LLBC_sharp_symbolic intT; y := LLBC_sharp_symbolic intT; z := bot; cond := bot]};
  anons := empty;
  abstractions := empty;
|}.

Definition lx : loan_id := 1%positive.
Definition ly : loan_id := 2%positive.
Definition lz : loan_id := 3%positive.

Definition A : positive := 1.

(** The join state at the end of the conditional. *)
Definition join_state : LLBC_sharp_state := {|
  vars := {[
    x := loan^m(intT, lx);
    y := loan^m(intT, ly);
    z := borrow^m(lz, LLBC_sharp_symbolic intT);
    cond := LLBC_sharp_symbolic boolT
  ]};
  anons := empty;
  abstractions := {[
    A := {[1%positive := borrow^m(lx, LLBC_sharp_symbolic intT);
           2%positive := borrow^m(ly, LLBC_sharp_symbolic intT);
           3%positive := loan^m(intT, lz)]} ]}
|}.

Section Eval_LLBC_sharp_program.
  Hint Rewrite (@alter_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@alter_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using discriminate : core.
  Hint Rewrite (@alter_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@delete_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using reflexivity : core.
  Hint Rewrite (@delete_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using congruence : core.
  Hint Rewrite (@delete_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  Lemma insert_empty_is_singleton `{FinMap K M} {V} k v : insert (M := M V) k v empty = {[k := v]}.
  Proof. reflexivity. Qed.
  Hint Rewrite (@insert_empty_is_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  (* Perform simplifications to put maps of the state in the form [{[x0 := v0; ...; xn := vn]}],
     that is a notation for a sequence of insertions applied to a singleton.
     We cannot use the tactic [vm_compute] because it computes under the insertions and the
     singleton. *)
  Ltac simpl_state :=
    (* We can actually perform vm_compute on sget, because the result is a value and not a state. *)
    repeat (remember (sget _ _ ) eqn:EQN; vm_compute in EQN; subst);
    compute - [insert alter empty singletonM delete leq_symbolic];
    autorewrite with core.

  Lemma safe_f : exists end_state, init_state |-{stmt} f ~>{1} end_state.
  Proof.
    eexists.
    eapply eval_seq_unit.
    (* Evaluation of the computation << x <= y >>. The result is stored in the temporary variable [cond]. *)
    { eapply LLBC_plus_E_Assign; [ | apply Store with (a := 1%positive)].
      - econstructor.
        + econstructor. eval_var. constructor. constructor. constructor.
        + econstructor. eval_var. constructor. constructor. constructor.
        + constructor.
      - eval_var. constructor.
      - apply decide_not_contains_outer_loan_correct. reflexivity.
      - apply store_compatible_types_nil.
      - reflexivity.
    }
    simpl_state. eapply eval_seq_unit.

    (* Evaluation of the conditional. *)
    { eapply LLBC_plus_IfThenElse_Symbolic with (B_join := {[rUnit := join_state]}).
      { econstructor. eval_var. constructor. econstructor. constructor. }

      (* Evaluation of the if branch. *)
      { eapply LLBC_plus_E_Assign; [ | apply Store with (a := 2%positive)].
        + apply Eval_mut_borrow with (l := lx).
          * eval_var. constructor.
          * compute_done.
          * compute_done.
          * compute_done.
          * constructor.
        + eval_var. constructor.
        + apply decide_not_contains_outer_loan_correct. constructor.
        + apply store_compatible_types_nil.
        + reflexivity. }

      (* Evaluation of the else branch. *)
      { eapply LLBC_plus_E_Assign; [ | apply Store with (a := 2%positive)].
        + apply Eval_mut_borrow with (l := ly).
          * eval_var. constructor.
          * compute_done.
          * compute_done.
          * compute_done.
          * constructor.
        + eval_var. constructor.
        + apply decide_not_contains_outer_loan_correct. constructor.
        + apply store_compatible_types_nil.
        + reflexivity. }

      apply is_join_singletons.
      (* The state [S_join] is more abstract than the state at the end of the if branch. *)
      { simpl_state.
        eapply prove_leq_symbolic.
        { eapply Leq_Reborrow_MutBorrow_Abs with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive) (kb := 1%positive) (kl := 3%positive); try compute_done.
          eapply var_not_in_abstraction; reflexivity. reflexivity. constructor. }
        simpl_state.
        eapply prove_leq_symbolic.
        { eapply Leq_Fresh_MutLoan_Abs with (sp := (encode_var y, [])) (l' := ly) (i := 2%positive) (k := 2%positive);
            [compute_done | now eapply var_not_in_abstraction | compute_done.. | constructor]. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_abstraction 1%positive. remove_abstraction 2%positive.
          eapply Leq_MergeAbs; [reflexivity.. | | discriminate].
          econstructor. eexists. split. constructor.
          eapply UnionInsert with (j := 2%positive); [reflexivity.. | ].
          apply UnionEmpty. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])). constructor. all: compute_done. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 1%positive. apply Leq_RemoveAnon. all: compute_done. }
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 2%positive. apply Leq_RemoveAnon. all: compute_done. }
        reflexivity. }

      (* The state [S_join] is more abstract than the state at the end of the else branch. *)
      { eapply prove_leq_symbolic.
        { eapply Leq_Reborrow_MutBorrow_Abs with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive) (kb := 2%positive) (kl := 3%positive); try compute_done.
          eapply var_not_in_abstraction; reflexivity. reflexivity. constructor. }
        simpl_state.
        eapply prove_leq_symbolic.
        { eapply Leq_Fresh_MutLoan_Abs with (sp := (encode_var x, [])) (l' := lx) (i := 2%positive) (k := 1%positive);
            [compute_done | now eapply var_not_in_abstraction | compute_done.. | constructor]. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_abstraction 1%positive. remove_abstraction 2%positive.
          apply Leq_MergeAbs; [reflexivity.. | | discriminate].
          econstructor. eexists. split. constructor.
          eapply UnionInsert with (j := 1%positive); [reflexivity.. | ].
          apply UnionEmpty. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])); [constructor | compute_done..]. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 1%positive. apply Leq_RemoveAnon. all: compute_done. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 2%positive. apply Leq_RemoveAnon. all: compute_done. }
        reflexivity. }
    }

    (* Execution of the line << *z += 1 >> *)
    eapply eval_seq_unit.
    { eapply LLBC_plus_E_Assign; [ | apply Store with (a := 1%positive)].
      - econstructor.
        + eapply Eval_copy.
          * eval_var. repeat econstructor || easy.
          * constructor. constructor.
        + apply Eval_IntConst.
        + constructor.
      - eval_var. repeat econstructor || easy.
      - cbn. apply decide_not_contains_outer_loan_correct. reflexivity.
      - eapply store_compatible_types_borrow; constructor.
      - reflexivity.
    }
    simpl_state.

    (* In order to access the variable << x >>, we must perform reorganizations in order to end the loan [lx.] *)
    eapply LLBC_plus_E_Reorg.
    { etransitivity.
      (* Ending the loan [lz] ... *)
      { constructor.
        eapply Reorg_end_borrow_m_in_abstraction
          with (i' := 1%positive) (j' := 3%positive) (q := (encode_var 3%positive, [])).
        - reflexivity.
        - reflexivity.
        - constructor.
        - compute_done.
        - intros ? ?. apply not_strict_prefix_nil.
        - eapply var_not_in_abstraction. reflexivity. }
      simpl_state. etransitivity.
      (* ... so that we could end the region abstraction ... *)
      { constructor.
        remove_abstraction 1%positive. apply Reorg_end_abstraction.
        - reflexivity.
        - compute_done.
        - constructor. cbn. apply UnionInsert with (j := 2%positive); [reflexivity.. | ].
         apply UnionInsert with (j := 3%positive); [reflexivity.. | ].
          apply UnionEmpty.
      }
      simpl_state.
      (* ... so that we could end the loan [lx]. *)
      { constructor.
        eapply Reorg_end_borrow_m with (p := (encode_var 1%positive, []))
                                       (q := (encode_anon 2%positive, [])).
        - reflexivity.
        - reflexivity.
        - constructor.
        - compute_done.
        - intros ? ?. apply not_strict_prefix_nil.
        - left. discriminate.
        - eapply var_not_in_abstraction. reflexivity.
        - eapply anon_not_in_abstraction. reflexivity. }
    }
    simpl_state.

    (* Execution of the line << x += 2 >> *)
    eapply LLBC_plus_E_Assign; [ | apply Store with (a := 5%positive)].
    - econstructor.
      + eapply Eval_copy; [eval_var | ]; constructor. constructor.
      + constructor.
      + constructor.
    - eval_var. constructor.
    - apply decide_not_contains_outer_loan_correct. reflexivity.
    - apply store_compatible_types_nil.
    - reflexivity.
  Qed.
End Eval_LLBC_sharp_program.

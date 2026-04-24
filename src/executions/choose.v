(** * Mechanized_LLBC.executions.choose : Execution of the choose function, LLBC# *)
From Stdlib Require Import List.
Import ListNotations.
From stdpp Require Import decidable pmap.
Require Import base PathToSubtree SimulationUtils lang.
Require Import Symbolic_states Symbolic_relations LLBC_sharp_semantics LLBC_sharp_exec_utils.

Open Scope option_monad_scope.
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
  vars := {[
    x := VSymbolic TInt;
    y := VSymbolic TInt;
    z := bot;
    cond := bot
  ]};
  anons := empty;
  abstractions := empty;
|}.

Definition lx : loan_id := 1%positive.
Definition ly : loan_id := 2%positive.
Definition lz : loan_id := 3%positive.

Definition A : positive := 1.

(** The join state at the end of the conditional. *)
Definition join_state : state := {|
  vars := {[
    x := loan^m(TInt, lx);
    y := loan^m(TInt, ly);
    z := borrow^m(lz, VSymbolic TInt);
    cond := VSymbolic TBool
  ]};
  anons := empty;
  abstractions := {[
    A := {[1%positive := borrow^m(lx, VSymbolic TInt);
           2%positive := borrow^m(ly, VSymbolic TInt);
           3%positive := loan^m(TInt, lz)]} ]}
|}.

Lemma safe_f : exists end_state, init_state |-# f ~> end_state.
Proof.
  eexists.
  eapply eval_seq_unit.
  (** Evaluation of the computation << x <= y >>. The result is stored in the temporary variable [cond]. *)
  { eapply assign_no_anon.
    { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  (** Evaluation of the conditional. *)
  eapply eval_seq_unit.
  { eapply LLBC_sharp_IfThenElse_Symbolic with (B := {[rUnit := join_state]});
      [ | eapply LLBC_sharp_Weaken_Postcondition..].
    { refine (try_compute (compute_eval_op _ _) _ _ _). reflexivity. }

    (** Evaluation of the if branch. *)
    { eapply assign_no_anon.
      { refine (try_compute (compute_borrow_mut lx _ _) _ _ _). reflexivity. }
      { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
    }

    (** The state [join_state] is more abstract than the state at the end of the if branch. *)
    { apply leq_singleton. unfold branching_state. simpl_map. simpl_state.
      eapply prove_leq_symbolic.
      { eapply Leq_Reborrow_MutBorrow_Abs
          with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive)
               (kb := 1%positive) (kl := 3%positive);
          try compute_done.
        eapply var_not_in_abstraction; reflexivity. reflexivity. constructor. }
      simpl_state.
      eapply prove_leq_symbolic.
      { eapply Leq_Fresh_MutLoan_Abs
          with (sp := (encode_var y, [])) (l' := ly) (i := 2%positive) (k := 2%positive);
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
      reflexivity. }

    (** Evaluation of the else branch. *)
    { eapply assign_no_anon.
      { refine (try_compute (compute_borrow_mut ly _ _) _ _ _). reflexivity. }
      { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
    }

    (** The state [join_state] is more abstract than the state at the end of the else branch. *)
    (* TODO: computation procedures for relation steps. *)
    { apply leq_singleton. unfold branching_state. simpl_map. simpl_state.
      eapply prove_leq_symbolic.
      { eapply Leq_Reborrow_MutBorrow_Abs
          with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive)
                      (kb := 2%positive) (kl := 3%positive);
          try compute_done.
        eapply var_not_in_abstraction; reflexivity. reflexivity. constructor. }
      simpl_state.
      eapply prove_leq_symbolic.
      { eapply Leq_Fresh_MutLoan_Abs
          with (sp := (encode_var x, [])) (l' := lx) (i := 2%positive) (k := 1%positive);
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
      reflexivity. }
  }

  (* Execution of the line << *z += 1 >> *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  (** In order to access the variable << x >>, we must perform reorganizations in order to end the loan [lx.] *)
  eapply LLBC_sharp_E_Reorg.
  { etransitivity.
    (* TODO: computation procedures for reorganization steps. *)
    (** Ending the loan [lz] ... *)
    { constructor.
      eapply Reorg_End_MutBorrow_in_abstraction
        with (i' := 1%positive) (j' := 3%positive) (q := (encode_var 3%positive, [])).
      - reflexivity.
      - reflexivity.
      - constructor.
      - compute_done.
      - intros ? ?. apply not_strict_prefix_nil.
      - eapply var_not_in_abstraction. reflexivity. }
    simpl_state. etransitivity.
    (** ... so that we could end the region abstraction ... *)
    { constructor.
      remove_abstraction 1%positive. apply Reorg_End_Abstraction.
      - reflexivity.
      - compute_done.
      - constructor. cbn. apply UnionInsert with (j := 2%positive); [reflexivity.. | ].
       apply UnionInsert with (j := 3%positive); [reflexivity.. | ].
        apply UnionEmpty.
    }
    simpl_state.
    (** ... so that we could end the loan [lx]. *)
    { constructor.
      eapply Reorg_End_MutBorrow with (p := (encode_var 1%positive, []))
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

  (** Execution of the line << x += 2 >> *)
  eapply assign_no_anon.
  { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
  { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
Qed.

(** * Mechanized_LLBC.executions.loop : Execution of loop, LLBC# *)
(** TODO: execute this code in LLBC to check that it runs as intended. *)
From Stdlib Require Import List.
Import ListNotations.
From stdpp Require Import decidable pmap.
Require Import base PathToSubtree SimulationUtils lang.
Require Import LLBC_sharp_states LLBC_sharp_relations LLBC_sharp_semantics LLBC_sharp_exec_utils.

(** The program we execute is:
<<
fn f(mut a : i32, n : i32) {
    let mut b = &mut a;
    for _ in 0..n {
        b = &mut *b;
        *b += 1;
   }
}
>>
  It is desugared as:
<<
fn f(mut a : i32, n : i32) {
    let mut b = &mut a;
    let mut i = 0;
    loop {
        let cond = n <= i;
        if cond {
            break;
        }
        else {
            i += 1;
            b = &mut *b;
            *b += 1;
            continue;
        }
    }
}
>>
 *)
Notation a := 1%positive.
Notation n := 2%positive.
Notation b := 3%positive.
Notation i := 4%positive.
Notation cond := 5%positive.

(* TODO: solve scope issues. *)
Close Scope stdpp_scope.

(** Note that we have to introduce a temporary variable [cond] to store the result of the comparison. *)
Definition f :=
  ASSIGN (b, []) <- &mut (a, []) ;;
  ASSIGN (i, []) <- Use (Const (IntConst 0)) ;;
  LOOP {{
    ASSIGN (cond, []) <- BinaryOp BLe (Copy (n, [])) (Copy (i, [])) ;;
    IF Copy (cond, []) {{
      Break
    }}
    ELSE {{
      ASSIGN (i, []) <- BinaryOp BAdd (Copy (i, [])) (Const (IntConst 1)) ;;
      ASSIGN (b, []) <- &mut (b, [Deref]) ;;
      ASSIGN (b, [Deref]) <- BinaryOp BAdd (Copy (b, [Deref])) (Const (IntConst 1)) ;;
      Continue
    }}
  }}
.

Open Scope stdpp.
(** We execute the function [f] on the most general state. The arguments << x >> and << y >> are initialized as symbolic values, while the local variables are uninitialized. *)
Definition init_state := {|
  vars := {[
    a := VSymbolic TInt;
    n := VSymbolic TInt;
    b := bot;
    i := bot;
    cond := bot
  ]};
  anons := empty;
  abstractions := empty;
|}.

Definition l0 : loan_id := 1%positive.
Definition l1 : loan_id := 2%positive.
Definition l2 : loan_id := 3%positive.

Definition A : positive := 1.

(** The loop invariant. *)
Definition S_inv : state := {|
  vars := {[
    a := loan^m(TInt, l0);
    b := borrow^m(l1, VSymbolic TInt);
    i := VSymbolic TInt;
    n := VSymbolic TInt;
    cond := bot
  ]};
  anons := empty;
  abstractions := {[
    A := {[1%positive := borrow^m(l0, VSymbolic TInt);
           2%positive := loan^m(TInt, l1)]} ]}
|}.

Definition B_inv : branching_state := {[rBreak := S_inv; rContinue := S_inv]}.

Lemma safe_f : exists end_state, init_state |-# f ~> end_state.
Proof.
  eexists.
  (** Evaluation of the assignment << b = &mut a >> *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_borrow_mut l0 _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  (** Evaluation of the assignment << i = 0 >> *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  (** The loop invariant is satisfied when entering the loop. *)
  apply LLBC_sharp_Weaken_Precondition with (Sr := S_inv).
  { eapply prove_leq_symbolic.
    { apply Leq_Reborrow_MutBorrow_Abs
        with (sp := (encode_var b, [])) (l1 := l1) (i := 1%positive)
              (kb := 1%positive) (kl := 2%positive).
      - compute_done.
      - compute_done.
      - eapply var_not_in_abstraction. reflexivity.
      - reflexivity.
      - discriminate.
      - constructor. }
    simpl_state.
    eapply prove_leq_symbolic; [constructor | ].
    { apply Leq_ToSymbolic with (sp := (encode_var i, [])).
      - constructor.
      - compute_done.
      - compute_done. }
    reflexivity. }

  (** We only have to prove that [B_inv] is the loop invariant. *)
  apply LLBC_sharp_E_Loop_Invariant with (Binv := B_inv); [ | reflexivity..].
  (** Evaluation of the computation << x <= y >>. The result is stored in the temporary variable [cond]. *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  (** Evaluation of the conditional. *)
  { eapply LLBC_sharp_IfThenElse_Symbolic; [ | eapply LLBC_sharp_Weaken_Postcondition..].
    { refine (try_compute (compute_eval_op _ _) _ _ _). reflexivity. }

    (** Evaluation of the if branch (<< break >>). *)
    { apply LLBC_sharp_E_Break. }

    (** The invariant is satisfied when breaking from the loop. *)
    (** We only need to unitialize the binding << cond |-> true >> *)
    { apply leq_singleton. unfold B_inv. simpl_map.
      eexists. split; [reflexivity | ].
      refine (try_compute (compute_uninitialize_value (encode_var cond, []) _) _ _ _).
      reflexivity. }

    (** Evaluation of the else branch. *)
    { (** Evaluation of the incrementation << i += 1 >> *)
      eapply eval_seq_unit.
      { eapply assign_no_anon.
        { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
        { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
      }
      simpl_state.
      (** Evaluation of the reborrow << b = *b >> *)
      eapply eval_seq_unit.
      { eapply LLBC_sharp_E_Assign.
        { refine (try_compute (compute_borrow_mut l2 _ _) _ _ _). reflexivity. }
       { refine (try_compute (compute_eval_store 1%positive _ _) _ _ _). reflexivity. }
      }
      simpl_state.
      (** Evaluation of the assigment << *b += 1 >> *)
      eapply eval_seq_unit.
      { eapply assign_no_anon.
        { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
        { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
      }
      simpl_state.
      apply LLBC_sharp_E_Continue. }

    (** The invariant is satisfied when continuing the loop. *)
    { apply leq_singleton. unfold B_inv. simpl_map.
      (** Unitializing the binding << cond |-> false >>. *)
      eapply prove_leq_symbolic; [ | ].
      { refine (try_compute (compute_uninitialize_value (encode_var cond, []) _) _ _ _).
        reflexivity. }
      simpl_state.
      (** Turning the anonymous binding << _ |-> borrow^m(l1, loan^m(int, l2)) >> into
         an abstraction. *)
      eapply prove_leq_symbolic; [constructor | ].
      { remove_anon 1%positive. apply Leq_ToAbs with (i := 2%positive); [reflexivity.. | ].
        apply ToAbs_MutReborrow with (kb := 1%positive) (kl := 2%positive). discriminate. }
      simpl_state.
      (** Merging the abstractions, and removing loan identifier [l1]. *)
      (* TODO: computation. *)
      eapply prove_leq_symbolic; [constructor | ].
      { remove_abstraction 1%positive. remove_abstraction 2%positive.
        apply Leq_MergeAbs; [reflexivity.. | | discriminate].
        eexists _, _. split.
        { eapply Remove_MutLoan with (i := 2%positive) (j := 1%positive).
          apply Remove_nothing. simpl_map. reflexivity. simpl_map. reflexivity. }
        { rewrite delete_insert_id by reflexivity. rewrite delete_insert_ne by discriminate.
          apply UnionInsert with (j := 2%positive); [reflexivity.. | ].
          apply UnionEmpty.
        }
      }
      simpl_state.
      (** Finally, we need to rename the loan [l2] into [l1]. We can do so because
        [l1] is fresh. *)
      exists S_inv. split; [ | reflexivity]. eapply prove_equiv_states; [ | reflexivity].
      exists {[l0 := l0; l2 := l1]}. split; [split | ]; compute_done.
    }
  }
Qed.

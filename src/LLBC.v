(** * Mechanized_LLBC.LLBC : definition of LLBC states. *)
Require Import base.
Require Import lang.
Require Import SimulationUtils.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Lia.
(* Notation conflict between stdpp's `+++` and our `+++`. That's why we're importing stpp first,
   then closing the scope. *)
From stdpp Require Import pmap.
Close Scope stdpp_scope.
Require Import PathToSubtree.
From Stdlib Require Bool.

(** * Definition of LLBC values and states. *)
Inductive value :=
| VBottom
| VInt (n : nat) (* TODO: use Aeneas integer types? *)
| VBool (b : bool)
| VMutLoan (l : loan_id)
| VMutBorrow (l : loan_id) (v : value)
.

Variant nodes :=
| NBottom
| NInt (n : nat)
| NBool (b : bool)
| NMutLoan (l : loan_id)
| NMutBorrow (l : loan_id)
.

Instance EqDecision_nodes : EqDecision nodes.
Proof. unfold RelDecision, Decision. repeat decide equality. Defined.

Definition LLBC_arity c := match c with
| NBottom => 0
| NInt _ => 0
| NBool _ => 0
| NMutLoan _ => 0
| NMutBorrow _ => 1
end.

Definition LLBC_get_node v := match v with
| VBottom => NBottom
| VInt n => NInt n
| VBool b => NBool b
| VMutLoan l => NMutLoan l
| VMutBorrow l _ => NMutBorrow l
end.

Definition LLBC_children v := match v with
| VBottom => []
| VInt _ => []
| VBool _ => []
| VMutLoan _ => []
| VMutBorrow _ v => [v]
end.

Definition LLBC_fold c vs := match c, vs with
| NInt n, [] => VInt n
| NBool b, [] => VBool b
| NMutLoan l, [] => VMutLoan l
| NMutBorrow l, [v] => VMutBorrow l v
| _, _ => VBottom
end.

Fixpoint LLBC_weight node_weight v :=
  match v with
  | VMutBorrow l v => node_weight (NMutBorrow l) + LLBC_weight node_weight v
  | v => node_weight (LLBC_get_node v)
end.

Program Instance ValueLLBC : Value value nodes := {
  arity := LLBC_arity;
  get_node := LLBC_get_node;
  children := LLBC_children;
  fold_value := LLBC_fold;
  vweight := LLBC_weight;
  bot := VBottom;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_nodes eq_children; inversion eq_nodes; inversion eq_children; reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; cbn; lia. Qed.

Record state := {
  vars : Pmap value;
  anons : Pmap value;
}.

Definition encode_var (x : var) := encode (A := var + anon) (inl x).
Definition encode_anon (a : positive) := encode (A := var + anon) (inr a).

Program Instance IsState : State state value := {
  extra := unit;
  get_map S := sum_maps (vars S) (anons S);
  get_extra _ := ();
  alter_at_accessor f a S :=
    match decode' (A := var + positive) a with
    | Some (inl x) => {| vars := alter f x (vars S); anons := anons S|}
    | Some (inr a) => {| vars := vars S; anons := alter f a (anons S)|}
    | None => S
    end;
  anon_accessor := encode_anon;
  accessor_anon x :=
    match decode (A := var + positive) x with
    | Some (inr a) => Some a
    | _ => None
    end;
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S)|};
}.
Next Obligation. intros [? ?] [? ?]. cbn. intros (-> & ->)%sum_maps_eq _. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ? ? i. cbn. destruct (decode' i) eqn:H.
  - rewrite decode'_is_Some in H.
    destruct s; cbn; rewrite <-H; symmetry;
      first [apply sum_maps_alter_inl | apply sum_maps_alter_inr].
  - symmetry. apply alter_id', sum_maps_lookup_None. assumption.
Qed.
(* What are the two following obligations? *)
Next Obligation. discriminate. Qed.
Next Obligation. discriminate. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros. cbn. unfold encode_anon. rewrite sum_maps_insert_inr. reflexivity. Qed.
Next Obligation. intros. unfold encode_anon. reflexivity. Qed.

Declare Scope llbc_scope.
Delimit Scope llbc_scope with llbc.

(* Notation "'bot'" := VBottom: llbc_scope. *)
Notation "'loan^m' ( l )" := (VMutLoan l) : llbc_scope.
Notation "'borrow^m' ( l  , v )" := (VMutBorrow l v) : llbc_scope.

Notation "'nbot'" := NBottom: llbc_scope.
Notation "'nloan^m' ( l )" := (NMutLoan l) : llbc_scope.
Notation "'nborrow^m' ( l )" := (NMutBorrow l) : llbc_scope.

(* Bind Scope llbc_scope with value. *)
Open Scope llbc_scope.

(** * Semantics of LLBC *)
Inductive eval_proj (S : state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| E_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = nborrow^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| E_Path_Nil pi : eval_path S perm [] pi pi
| E_Path_Proj proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm (p : place) pi :=
  let pi_0 := (encode_var (fst p), []) in
  valid_spath S pi_0 /\ eval_path S perm (snd p) (encode_var (fst p), []) pi.

Local Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
Qed.

Lemma eval_path_valid (s : state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof. destruct H as (? & ?). eapply eval_path_valid; eassumption. Qed.
Hint Resolve eval_place_valid : spath.

Variant is_loan : nodes -> Prop :=
| IsLoan_MutLoan l : is_loan (nloan^m(l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = nbot) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> nbot) => discriminate : spath.

Variant is_mut_borrow : nodes -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (nborrow^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).

Lemma loan_is_not_bot x : is_loan x -> x <> nbot. Proof. intros [ ]; discriminate. Qed.

Inductive copy_val : value -> value -> Prop :=
| Copy_val_int (n : nat) : copy_val (VInt n) (VInt n)
| Copy_val_bool (b : bool) : copy_val (VBool b) (VBool b)
.

Variant eval_operand : operand -> state -> (value * state) -> Prop :=
| E_IntConst S n : S |-{op} Const (IntConst n) => (VInt n, S)
| E_BoolConst S n : S |-{op} Const (IntConst n) => (VInt n, S)
| E_Copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| E_Move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

Definition get_loan_id c :=
  match c with
  | nloan^m(l) => Some l
  | nborrow^m(l) => Some l
  | _ => None
  end.

Notation is_fresh l S := (not_state_contains (fun c => get_loan_id c = Some l) S).

Variant eval_binary_op : BinOp -> value -> value -> value -> Prop :=
  | E_Add m n :
      eval_binary_op BAdd (VInt m) (VInt n) (VInt (m + n))
  | E_Le m n :
      eval_binary_op BLe (VInt m) (VInt n) (VBool (m <=? n))
.

Variant eval_rvalue : rvalue -> state -> (value * state) -> Prop :=
  | E_Use op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Use op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | E_BinOp S S' S'' binop op_l op_r vl vr w :
      (S |-{op} op_l => (vl, S')) ->
      (S' |-{op} op_r => (vr, S'')) ->
      eval_binary_op binop vl vr w ->
      S |-{rv} (BinaryOp binop op_l op_r) => (w, S'')
  | E_MutBorrow S p pi l : S |-{p} p =>^{Mut} pi ->
      not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) -> is_fresh l S ->
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(l)])
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Definition not_in_borrow (S : state) p :=
  forall q, prefix q p -> is_mut_borrow (get_node (S.[q])) -> q = p.

Inductive reorg : state -> state -> Prop :=
| Reorg_End_MutBorrow S (p q : spath) l :
    disj p q -> get_node (S.[p]) = nloan^m(l) -> get_node (S.[q]) = nborrow^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : value * state -> state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : (S,, a |-> v) |-{p} p =>^{Mut} sp)
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

(* TODO: take fuel into account and delete this notation. *)
Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).

Inductive eval_stmt : statement -> flow_token -> state -> state -> Prop :=
  | E_Nop S : S |-{stmt} Nop => rUnit, S
  | E_Panic S : S |-{stmt} Panic => rPanic, S
  | E_Seq_Unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
      (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :  S0 |-{stmt} stmt_l;; stmt_r => r, S2
  | E_Seq_Propagate S0 S1 stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
      S0 |-{stmt} stmt_l;; stmt_r => rPanic, S1
  | E_Assign S vS' S'' p rv : (S |-{rv} rv => vS') -> store p vS' S'' ->
      S |-{stmt} ASSIGN p <- rv => rUnit, S''
  | E_IfThenElse_T S S' S'' cond stmt_if stmt_else r
      (eval_cond : S |-{op} cond => (VBool true, S')) :
      S' |-{stmt} stmt_if => r, S'' ->
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) => r, S''
  | E_IfThenElse_F S S' S'' cond stmt_if stmt_else r
      (eval_cond : S |-{op} cond => (VBool false, S')) :
      S' |-{stmt} stmt_else => r, S'' ->
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) => r, S''
  | E_Reorg S0 S1 S2 stmt r (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt => r, S2) :
      S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

(** * Execution of a LLBC program. *)
Local Open Scope option_monad_scope.
(** The program we execute is:
<<
fn main() {
    let mut a = 1983;
    let mut b = 1986;
    let mut c = &mut a;
    let d = &mut *c;
    c = &mut b;
    *d = 58;
}
>>
 *)
Notation a := 1%positive.
Notation b := 2%positive.
Notation c := 3%positive.
Notation d := 4%positive.
Definition main : statement :=
  ASSIGN (a, []) <- Use (Const (IntConst 1983)) ;;
  ASSIGN (b, []) <- Use (Const (IntConst 1986)) ;;
  ASSIGN (c, []) <- &mut (a, []) ;;
  ASSIGN (d, []) <- &mut (c, [Deref]) ;;
  ASSIGN (c, []) <- &mut (b, []) ;;
  ASSIGN (d, [Deref]) <- Use (Const (IntConst 58)) ;;
  Nop
.
(** Note: the line << c = &mut b >> overwrites a loan, but as it is an outer loan, it does
   not cause any problem. This is a check that the overwriting of outer loans is supported.

   Also, the last [Nop] statement was added so that we could perform reorganization operations
   before the end, and but back the value 58 in the variable [a]. *)

Open Scope stdpp.
Notation init_state := {|
  vars := {[a := bot; b := bot; c := bot; d := bot]};
  anons := empty;
|}.

Definition decide_not_contains_outer_loan v :=
  match v with
  | loan^m(l) => false
  | _ => true
  end.

(* TODO: move in PathToSubtree.v *)
Lemma valid_vpath_no_children v p (valid_p : valid_vpath v p) (H : children v = []) : p = [].
Proof.
  induction valid_p as [ | ? ? ? ? G].
  - reflexivity.
  - rewrite H, nth_error_nil in G. inversion G.
Qed.

(** For the moment, the type of values is so restricted that a value contains an outer loan if and
    only if it is a mutable loan. *)
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

Instance decidable_not_value_contains P `(H : forall n, Decision (P n)) v :
  Decision (not_value_contains P v).
Proof.
  induction v; try (apply decidable_not_value_contains_zeroary; [assumption | reflexivity]).
  eapply decidable_not_value_contains_unary; reflexivity || assumption.
Defined.

Instance decidable_is_loan c : Decision (is_loan c).
Proof. destruct c; first [left; constructor | right; inversion 1]. Defined.

Instance decidable_is_mut_borrow c : Decision (is_mut_borrow c).
Proof. destruct c; first [left; constructor | right; inversion 1]. Defined.

Instance decidable_is_fresh l S : Decision (is_fresh l S).
Proof. apply decidable_not_state_contains. solve_decision. Defined.

(* Note: an alternative to using tactics is to define functions, and prove their correction. *)

(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
Ltac eval_var :=
  split; [eexists; split; [reflexivity | constructor] | ].

Section Eval_LLBC_program.
  Hint Rewrite (@alter_insert_eq _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@alter_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using discriminate : core.
  Hint Rewrite (@alter_singleton_eq _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  Lemma insert_empty_is_singleton `{FinMap K M} {V} k v : insert (M := M V) k v empty = {[k := v]}.
  Proof. reflexivity. Qed.
  Hint Rewrite (@insert_empty_is_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  (* Perform simplifications to put maps of the state in the form `{[x0 := v0; ...; xn := vn]}`,
     that is a notation for a sequence of insertions applied to a singleton.
     We cannot use the tactic `vm_compute` because it computes under the insertions and the
     singleton. *)
  Ltac simpl_state :=
    (* We can actually perform vm_compute on sget, because the result is a value and not a state. *)
    repeat (remember (sget _ _ ) eqn:EQN; vm_compute in EQN; subst);
    compute - [insert alter empty singleton];
    autorewrite with core.

  Lemma safe_main :
    exists end_state, eval_stmt main rUnit init_state end_state /\
      exists pi, eval_place end_state Imm ((a, []) : place) pi /\ end_state.[pi] = VInt 58.
  Proof.
    eexists. split. {
      eapply E_Seq_Unit.
      { eapply E_Assign; [ | apply Store with (a := 1%positive)].
        - apply E_Use, E_IntConst.
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | apply Store with (a := 2%positive)].
        - apply E_Use, E_IntConst.
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 3%positive)].
        - apply E_MutBorrow with (l := 1%positive);
            [eval_var; constructor | compute_done..].
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 4%positive)].
        - eapply E_MutBorrow with (l := 2%positive).
          + eval_var. repeat econstructor || easy.
          + compute_done.
          + compute_done.
          + compute_done.
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 5%positive)].
        - apply E_MutBorrow with (l := 3%positive); [eval_var; constructor | compute_done..].
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 6%positive)].
        - apply E_Use, E_IntConst.
        - eval_var. repeat econstructor || easy.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Reorg.
      { etransitivity; [constructor | ].
        { apply Reorg_End_MutBorrow with (p := (encode_anon 5, [0])) (q := (encode_var d, [])) (l := 2%positive).
          + left. discriminate.
          + reflexivity.
          + reflexivity.
          + compute_done.
          + intros ? ->%prefix_nil. reflexivity. }
          simpl_state.
          constructor.
          apply Reorg_End_MutBorrow with (l := 1%positive) (p := (encode_var a, [])) (q := (encode_anon 5, [])).
          + left. discriminate.
          + reflexivity.
          + reflexivity.
          + compute_done.
          + intros ? ->%prefix_nil. reflexivity.
      }
      simpl_state. apply E_Nop.
    }
    eexists. split.
    - eval_var. constructor.
    - vm_compute. reflexivity.
  Qed.
End Eval_LLBC_program.

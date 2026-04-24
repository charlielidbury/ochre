(** * Mechanized_LLBC.LLBC_sharp : Semantics of LLBC+ and LLBC#. *)
From stdpp Require Import pmap gmap.
Require Import base OptionMonad PathToSubtree SimulationUtils lang.
Require Import Symbolic_states Symbolic_relations.

(** * Semantics of LLBC## *)
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
  valid_spath S pi_0 /\ eval_path S perm (snd p) pi_0 pi.
(* TODO: reserved notation. *)
Global Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi)
  (at level 50) : llbc_sharp_scope.

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

Definition copiable (ty : LLBC_type) := True.

Inductive copy_val : value -> value -> Prop :=
| Copy_val_int (n : nat) : copy_val (VInt n) (VInt n)
| Copy_val_bool (b : bool) : copy_val (VBool b) (VBool b)
| Copy_val_symbolic ty : copiable ty ->
    copy_val (VSymbolic ty) (VSymbolic ty)
.

Variant eval_operand : operand -> state -> (value * state) -> Prop :=
| E_IntConst S n : S |-{op} Const (IntConst n) => (VInt n, S)
| E_BoolConst S b : S |-{op} Const (BoolConst b) => (VBool b, S)
| E_Copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| E_Move S (p : place) pi (Heval : eval_place S Mov p pi)
    (move_no_loan : not_contains_loan (S.[pi])) (move_no_bot : not_contains_bot (S.[pi])) :
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r) : llbc_sharp_scope.

Variant eval_binary_op : BinOp -> value -> value -> value -> Prop :=
  | E_Add_int_int m n :
      eval_binary_op BAdd (VInt m) (VInt n) (VInt (m + n))
  | E_Add_int_symbolic m :
      eval_binary_op BAdd (VInt m) (VSymbolic TInt) (VSymbolic TInt)
  | E_Add_symbolic_int n :
      eval_binary_op BAdd (VSymbolic TInt) (VInt n) (VSymbolic TInt)
  | E_Add_symbolic_symbolic :
      eval_binary_op BAdd (VSymbolic TInt) (VSymbolic TInt) (VSymbolic TInt)
  | E_Le_int_int m n :
      eval_binary_op BLe (VInt m) (VInt n) (VBool (m <=? n))
  | E_Le_int_symbolic m :
      eval_binary_op BLe (VInt m) (VSymbolic TInt) (VSymbolic TBool)
  | E_Le_symbolic_int n :
      eval_binary_op BLe (VSymbolic TInt) (VInt n) (VSymbolic TBool)
  | E_Le_symbolic_symbolic :
      eval_binary_op BLe (VSymbolic TInt) (VSymbolic TInt) (VSymbolic TBool)
.

Variant eval_rvalue : rvalue -> state -> (value * state) -> Prop :=
  | E_Use op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Use op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | E_BinOp S S' S'' binop op_0 op_1 v0 v1 w
      (eval_op_0 : S |-{op} op_0 => (v0, S')) (eval_op_1 : S' |-{op} op_1 => (v1, S''))
      (Hbinop : eval_binary_op binop v0 v1 w) :
      S |-{rv} (BinaryOp binop op_0 op_1) => (w, S'')
  (* Note: with a typing judgement on LLBC, and with a well-typedness invariant, the type
   * [ty] could be obtained from the type of the place p, and the well-typedness of
   * [S.[pi]] could be derived from the well-typedness of [S]. *)
  | E_MutBorrow S p pi l ty (eval_p : S |-{p} p =>^{Mut} pi)
      (borrow_no_loan : not_contains_loan (S.[pi]))
      (borrow_no_bot : not_contains_bot (S.[pi]))
      (fresh_l : is_fresh l S)
      (Htype : is_of_type ty (S.[pi])) :
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(ty, l)])
where "S |-{rv} rv => r" := (eval_rvalue rv S r) : llbc_sharp_scope.

(* Note: we use the variable names i' and j' instead of i and j that are used for leq_state_base.
 * We are also using the name A' instead of A, B or C for the region abstractions.
 *)
Variant reorg : state -> state -> Prop :=
(* Ends a borrow when it's not in an abstraction: *)
| Reorg_End_MutBorrow S (p q : spath) l ty
    (get_loan : get_node (S.[p]) = nloan^m(ty, l)) (get_borrow : get_node (S.[q]) = nborrow^m(l))
    (type_borrow : is_of_type ty (S.[q +++ [0] ]))
    (Hno_loan : not_contains_loan (S.[q +++ [0] ])) (Hnot_in_borrow : not_in_borrow S q)
    (Hdisj : disj p q)
    (loan_not_in_abstraction : not_in_abstraction p)
    (borrow_not_in_abstraction : not_in_abstraction q) :
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
(* Ends a borrow when it's in an abstraction: *)
(* The value that is transferred back, S.[q +++ [0]], has to be of integer type. *)
| Reorg_End_MutBorrow_in_abstraction S q i' j' l ty
    (get_loan : abstraction_element S i' j' = Some (loan^m(ty, l)))
    (get_borrow : get_node (S.[q]) = nborrow^m(l))
    (type_borrow : is_of_type ty (S.[q +++ [0] ]))
    (Hno_loan : not_contains_loan (S.[q +++ [0] ])) (Hnot_in_borrow : not_in_borrow S q)
    (borrow_not_in_abstraction : not_in_abstraction q) :
    reorg S ((remove_abstraction_value S i' j').[q <- bot])
(* q refers to a path in abstraction A, at index j. *)
| Reorg_End_Abstraction S i' A' S'
    (fresh_i' : fresh_abstraction S i')
    (A_no_loans : map_Forall (fun _ => not_contains_loan) A')
    (Hadd_anons : add_anons S A' S') : reorg (S,,, i' |-> A') S'
.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : value * state -> state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : S |-{p} p =>^{Mut} sp)
  (no_outer_loan : not_contains_outer_loan (S.[sp]))
  (Hstore_type : store_compatible_types S sp v) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

(** Turning the state at the end of the last iteration of the loop into the state after the loop. *)
(** We simply need to rename the tags of each branch. *)
Definition end_loop (B : branching_state) : branching_state := pkmap end_loop_tag B.

Inductive LLBC_plus_eval_stmt : nat -> statement -> state -> branching_state -> Prop :=
  | LLBC_plus_E_Step_Zero s S : S |-{stmt} s ~>{0} empty
  | LLBC_plus_E_Nop n S : S |-{stmt} Nop ~>{1 + n} {[rUnit := S]}
  | LLBC_plus_E_Panic n S : S |-{stmt} Panic ~>{1 + n} {[rPanic := S]}
  | LLBC_plus_E_Break n S : S |-{stmt} Break ~>{1 + n} {[rBreak := S]}
  | LLBC_plus_E_Continue n S : S |-{stmt} Continue ~>{1 + n} {[rContinue := S]}
  | LLBC_plus_E_Seq_Propagate n S0 B1 stmt_0 stmt_1
      (eval_stmt_0 : S0 |-{stmt} stmt_0 ~>{1 + n} B1) (Hno_unit : lookup rUnit B1 = None) :
      S0 |-{stmt} (Seq stmt_0 stmt_1) ~>{1 + n} B1
  | LLBC_plus_E_Seq_Unit_Propagate n S0 B1 S_unit B_unit B_join stmt_0 stmt_1
      (eval_stmt_0 : S0 |-{stmt} stmt_0 ~>{1 + n} B1)
      (H_unit : lookup rUnit B1 = Some S_unit)
      (eval_stmt_1 : S_unit |-{stmt} stmt_1 ~>{1 + n} B_unit)
      (His_join : is_join B_unit (delete rUnit B1) B_join) :
      S0 |-{stmt} (Seq stmt_0 stmt_1) ~>{1 + n} B_join
  | LLBC_plus_E_Assign n S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-{stmt} ASSIGN p <- rv ~>{1 + n} {[rUnit := S'']}
  | LLBC_plus_E_IfThenElse_T n S S' B_if cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool true, S'))
      (Heval_if_branch : S' |-{stmt} stmt_if ~>{1 + n} B_if) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} B_if
  | LLBC_plus_E_IfThenElse_F n S S' B_else cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool false, S'))
      (Heval_else_branch : S' |-{stmt} stmt_else ~>{1 + n} B_else) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} B_else
  (* Note: in the ICFP'24 article, the symbolic value is replaced by a concrete boolean in each
     branch. We cannot do that as symbolic values are currently not named. *)
  | LLBC_plus_IfThenElse_Symbolic n S S' B_if B_else B_join cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VSymbolic TBool, S'))
      (Heval_if_branch : S' |-{stmt} stmt_if ~>{1 + n} B_if)
      (Heval_else_branch : S' |-{stmt} stmt_else ~>{1 + n} B_else)
      (His_join : is_join B_if B_else B_join) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} B_join
  | LLBC_plus_E_Reorg n S0 S1 B2 stmt (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt ~>{1 + n} B2) :
      S0 |-{stmt} stmt ~>{1 + n} B2
  (* We perform a single loop iteration, and stop because it does not continue. *)
  | LLBC_plus_E_Loop_Stop n S body B1
      (eval_body : S |-{stmt} body ~>{1 + n} B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (no_continue : lookup rContinue B1 = None) :
      S |-{stmt} (LOOP {{ body }}) ~>{1 + n} (end_loop B1)
  | LLBC_plus_E_Loop_Continue n S body B1 S1 B2 Bend
      (eval_body : S |-{stmt} body ~>{1 + n} B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (Hcontinue : lookup rContinue B1 = Some S1)
      (Heval2 : S1 |-{stmt} (LOOP {{ body }}) ~>{n} B2)
      (His_join : is_join (end_loop (delete rContinue B1)) B2 Bend) :
      S |-{stmt} (LOOP {{ body }}) ~>{1 + n} Bend
where "S |-{stmt} stmt ~>{ n } B" := (LLBC_plus_eval_stmt n stmt S B) : llbc_sharp_scope.

Inductive LLBC_sharp_eval_stmt : statement -> state -> branching_state -> Prop :=
  | LLBC_sharp_E_Nop S : S |-# Nop ~> {[rUnit := S]}
  | LLBC_sharp_E_Panic S : S |-# Panic ~> {[rPanic := S]}
  | LLBC_sharp_E_Break S : S |-# Break ~> {[rBreak := S]}
  | LLBC_sharp_E_Continue S : S |-# Continue ~> {[rContinue := S]}
  | LLBC_sharp_E_Seq_Propagate S0 B1 stmt_0 stmt_1
      (eval_stmt_0 : S0 |-# stmt_0 ~> B1) (Hno_unit : lookup rUnit B1 = None) :
      S0 |-# (Seq stmt_0 stmt_1) ~> B1
  | LLBC_sharp_E_Seq_Unit_Propagate S0 B1 S1 B2 stmt_0 stmt_1
      (eval_stmt_0 : S0 |-# stmt_0 ~> B1)
      (H_unit : lookup rUnit B1 = Some S1)
      (leq_B1_B2 : leq_branching (delete rUnit B1) B2)
      (eval_stmt_1 : S1 |-# stmt_1 ~> B2) :
      S0 |-# (Seq stmt_0 stmt_1) ~> B2
  | LLBC_sharp_E_Assign S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-# ASSIGN p <- rv ~> {[rUnit := S'']}
  | LLBC_sharp_E_IfThenElse_T S S' B_if cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool true, S'))
      (Heval_if_branch : S' |-# stmt_if ~> B_if) :
      S |-# (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~> B_if
  | LLBC_sharp_E_IfThenElse_F S S' B_else cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool false, S'))
      (Heval_else_branch : S' |-# stmt_else ~> B_else) :
      S |-# (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~> B_else
  (* Note: in the ICFP'24 article, the symbolic value is replaced by a concrete boolean in each
     branch. We cannot do that as symbolic values are currently not named. *)
  | LLBC_sharp_IfThenElse_Symbolic S S' B cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VSymbolic TBool, S'))
      (Heval_if_branch : S' |-# stmt_if ~> B)
      (Heval_else_branch : S' |-# stmt_else ~> B) :
      S |-# (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~> B
  | LLBC_sharp_E_Reorg S0 S1 B2 stmt (Hreorg : reorg^* S0 S1) (Heval : S1 |-# stmt ~> B2) :
      S0 |-# stmt ~> B2
  (* We perform a single loop iteration, and stop because it does not continue. *)
  | LLBC_sharp_E_Loop_Stop S body B1
      (eval_body : S |-# body ~> B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (no_continue : lookup rContinue B1 = None) :
      S |-# (LOOP {{ body }}) ~> (end_loop B1)
  | LLBC_sharp_E_Loop_Continue S0 body B1 S1 Bend
      (eval_body : S0 |-# body ~> B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (leq_B1_Bend : leq_branching (end_loop (delete rContinue B1)) Bend)
      (Hcontinue : lookup rContinue B1 = Some S1)
      (Heval2 : S1 |-# (LOOP {{ body }}) ~> Bend) :
       S0 |-# (LOOP {{ body }}) ~> Bend
  (* These are LLBC## only rules. *)
  | LLBC_sharp_E_Loop_Invariant body Sinv Binv
      (eval_body : Sinv |-# body ~> Binv)
      (inv_preservation : lookup rContinue Binv = Some Sinv)
      (no_unit : lookup rUnit Binv = None) :
      Sinv |-# (LOOP {{ body }}) ~> (end_loop (delete rContinue Binv))
  | LLBC_sharp_Weaken_Precondition s Sl Sr B
      (Hweaken : leq_symbolic Sl Sr) (Heval : Sr |-# s ~> B) :
      Sl |-# s ~> B
  | LLBC_sharp_Weaken_Postcondition s S Bl Br
      (Heval : S |-# s ~> Bl) (Hweaken : leq_branching Bl Br) :
      S |-# s ~> Br
where "S |-# stmt ~> B" := (LLBC_sharp_eval_stmt stmt S B) : llbc_sharp_scope.

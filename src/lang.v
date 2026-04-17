(** * Mechanized_LLBC.lang : Syntax of LLBC and general definitions. *)
Require Import base.
Require Import PathToSubtree.
From Stdlib Require Import PArith.
From stdpp Require Import pmap gmap.

Definition var := positive.

Variant proj :=
| Deref
| Field (f : nat).

(* Places are the syntactic way of denoting and accessing memory locations. Formally,
   a place is the combination of a variable, and a list of projections called a
   "path". Projections are ordered from the first to the last to be applied.

   Example: the place ( *x ).1 is represented the following way: (x, [*, .1])

   Do not mix paths (syntactical constructs of the language) with vpaths and spaths (the
   canonical way to denotes sub-values in a value of the state.)
*)
(* TODO: notation *)
Definition path := list proj.
Definition place : Set := var * path.

Variant const :=
| IntConst (n : nat) (* TODO: use Aeneas integer types? *)
| BoolConst (b : bool).

Variant operand :=
| Const (c : const)
| Move (p : place)
| Copy (p : place).

Variant BinOp :=
| BAdd
| BLe.

Variant rvalue :=
| Use (op : operand)
| BinaryOp (b : BinOp) (op_l : operand) (op_r : operand)
| BorrowMut (p : place).

Inductive statement :=
| Nop
| Assign (p : place) (rv : rvalue)
| Seq (stmt_0 : statement) (stmt_1 : statement)
(* Note: this should be generalized to match any enumerations, as booleans should only be a
 * particular type of enumeration. *)
| SwitchBool (op : operand) (stmt_if : statement) (stmt_else : statement)
| Loop (body : statement)
| Panic
| Break
| Continue
.


(* TODO: notation scope. *)
(* TODO: this notation conflicts with a stdpp notation. *)
Notation "s0 ;; s1" := (Seq s0 s1)
  (at level 100, s1 at level 200, only parsing, right associativity).
Notation "&mut p" := (BorrowMut p) (at level 80).
Notation "'ASSIGN' p <- rv" := (Assign p rv) (at level 90).
Notation "'IF'  op  {{  stmt_if  }}  'ELSE'  {{  stmt_else  }}" := (SwitchBool op stmt_if stmt_else)
  (at level 90).
Notation "'LOOP'  {{  body  }}" := (Loop body) (at level 90).

Local Open Scope positive_scope.
Check (&mut (1, nil)).
Check (ASSIGN (2, nil) <- &mut (1, nil)).
Check (ASSIGN (1, nil) <- Use (Const (IntConst 3))).
Check (ASSIGN (1, nil) <- Use (Const (IntConst 3)) ;; ((ASSIGN (2, nil) <- &mut (1, nil)) ;; Panic)).
Check (IF (Const (BoolConst true)) {{ Panic }} ELSE {{ Nop }}).

(* These definitions are not part of the grammar, but they are common for several (all?) semantics of the LLBC. *)
Definition loan_id := positive.

Variant permission := Imm | Mut | Mov.

(** LLBC is a langage with non-local control-flow management, with the << break >>, << continue >>, << panic >> and << return >> keywords. As such, statements yield a *control-flow token*, that determines the continuation of the computation. *)
Variant flow_token : Set :=
| rPanic
| rUnit (* Panicless termination. TODO: rename. *)
| rBreak
| rContinue
.

(** Control-flow tags can be keys for [gmap]. *)
Global Instance flow_token_eq_dec : EqDecision flow_token.
Proof. unfold EqDecision, Decision. decide equality. Qed.

Definition encode_flow_token r :=
  match r with
  | rPanic => 1%positive
  | rUnit => 2%positive
  | rBreak => 3%positive
  | rContinue => 4%positive
  end.

Definition decode_flow_token r :=
  match r with
  | 1%positive => Some rPanic
  | 2%positive => Some rUnit
  | 3%positive => Some rBreak
  | 4%positive => Some rContinue
  | _ => None
  end.

Program Global Instance flow_token_countable : Countable flow_token := {
  encode := encode_flow_token;
  decode := decode_flow_token
}.
Next Obligation. intros [ ]; reflexivity. Qed.

(** If the execution of the loop body ends on a token [r <> rContinue], computes the tag of the state after the loop. *)
Definition end_loop_tag r : option flow_token :=
  match r with
  (** If the loop ends on a break, the program continues as usual. *)
  | rBreak => Some rUnit
  (** Panics are propagated through the loop. *)
  | rPanic => Some rPanic
  (** Note that [end_loop_tag] is not defined for [rContinue] and [rUnit].
     - If the body ends on [rContinue], it loops back.
     - If the body ends on [rUnit], the behavior is not defined, the program gets stuck. *)
  | _ => None
  end.

Lemma partial_inj_end_loop_tag : partial_inj end_loop_tag.
Proof. intros r0 (? & H) r1. destruct r0; destruct r1; easy. Qed.

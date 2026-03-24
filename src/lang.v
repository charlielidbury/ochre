(** * Mechanized_LLBC.lang : syntax of LLBC. *)
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
| Just (op : operand)
| BinaryOp (b : BinOp) (op_l : operand) (op_r : operand)
| BorrowMut (p : place).

Inductive statement :=
| Nop
| Assign (p : place) (rv : rvalue)
| Seq (stmt_0 : statement) (stmt_1 : statement)
(* Note: this should be generalized to match any enumerations, as booleans should only be a
 * particular type of enumeration. *)
| SwitchBool (op : operand) (stmt_if : statement) (stmt_else : statement)
| Panic.


(* TODO: notation scope. *)
(* TODO: this notation conflicts with a stdpp notation. *)
Notation "s0 ;; s1" := (Seq s0 s1)
  (at level 100, s1 at level 200, only parsing, right associativity).
Notation "&mut p" := (BorrowMut p) (at level 80).
Notation "'ASSIGN' p <- rv" := (Assign p rv) (at level 90).
Notation "'IF'  op  {{ stmt_if }}  'ELSE'  {{ stmt_else }}" := (SwitchBool op stmt_if stmt_else)
  (at level 90).

Local Open Scope positive_scope.
Check (&mut (1, nil)).
Check (ASSIGN (2, nil) <- &mut (1, nil)).
Check (ASSIGN (1, nil) <- Just (Const (IntConst 3))).
Check (ASSIGN (1, nil) <- Just (Const (IntConst 3)) ;; ((ASSIGN (2, nil) <- &mut (1, nil)) ;; Panic)).
Check (IF (Const (BoolConst true)) {{ Panic }} ELSE {{ Nop }}).

(* These definitions are not part of the grammar, but they are common for several (all?) semantics of the LLBC. *)
Definition loan_id := positive.

Variant permission := Imm | Mut | Mov.

(* TODO: rename [control_flow_tag] *)
Variant statement_result : Set :=
| rPanic
| rUnit. (* Panicless termination. *)

(** Control-flow tags can be keys for [gmap]. *)
Global Instance stmt_result_eq_dec : EqDecision statement_result.
Proof. unfold EqDecision, Decision. decide equality. Qed.

Definition encode_stmt_result r :=
  match r with
  | rPanic => 1%positive
  | rUnit => 2%positive
  end.

Definition decode_stmt_result r :=
  match r with
  | 1%positive => Some rPanic
  | 2%positive => Some rUnit
  | _ => None
  end.

Program Global Instance stmt_result_countable : Countable statement_result := {
  encode := encode_stmt_result;
  decode := decode_stmt_result
}.
Next Obligation. intros [ ]; reflexivity. Qed.

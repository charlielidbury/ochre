(** * Mechanized_LLBC.LLBC_plus : Semantics of LLBC+. *)
(** All of the judgement are identical to LLBC##, except the evaluation of statements. *)
From stdpp Require Import fin_maps.
Require Import lang SimulationUtils Symbolic_states Symbolic_relations.
Require Import LLBC_sharp.

Declare Scope llbc_plus_scope.
Delimit Scope llbc_plus_scope with llbc_plus.

Inductive eval_stmt : nat -> statement -> state -> branching_state -> Prop :=
  | E_Step_Zero s S : S |-{stmt} s ~>{0} empty
  | E_Nop n S : S |-{stmt} Nop ~>{1 + n} {[rUnit := S]}
  | E_Panic n S : S |-{stmt} Panic ~>{1 + n} {[rPanic := S]}
  | E_Break n S : S |-{stmt} Break ~>{1 + n} {[rBreak := S]}
  | E_Continue n S : S |-{stmt} Continue ~>{1 + n} {[rContinue := S]}
  | E_Seq_Propagate n S0 B1 stmt_0 stmt_1
      (eval_stmt_0 : S0 |-{stmt} stmt_0 ~>{1 + n} B1) (Hno_unit : lookup rUnit B1 = None) :
      S0 |-{stmt} (Seq stmt_0 stmt_1) ~>{1 + n} B1
  | E_Seq_Unit_Propagate n S0 B1 S_unit B_unit B_join stmt_0 stmt_1
      (eval_stmt_0 : S0 |-{stmt} stmt_0 ~>{1 + n} B1)
      (H_unit : lookup rUnit B1 = Some S_unit)
      (eval_stmt_1 : S_unit |-{stmt} stmt_1 ~>{1 + n} B_unit)
      (His_join : is_join B_unit (delete rUnit B1) B_join) :
      S0 |-{stmt} (Seq stmt_0 stmt_1) ~>{1 + n} B_join
  | E_Assign n S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-{stmt} ASSIGN p <- rv ~>{1 + n} {[rUnit := S'']}
  | E_IfThenElse_T n S S' B_if cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool true, S'))
      (Heval_if_branch : S' |-{stmt} stmt_if ~>{1 + n} B_if) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} B_if
  | E_IfThenElse_F n S S' B_else cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool false, S'))
      (Heval_else_branch : S' |-{stmt} stmt_else ~>{1 + n} B_else) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} B_else
  (* Note: in the ICFP'24 article, the symbolic value is replaced by a concrete boolean in each
     branch. We cannot do that as symbolic values are currently not named. *)
  | E_IfThenElse_Symbolic n S S' B_if B_else B_join cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VSymbolic TBool, S'))
      (Heval_if_branch : S' |-{stmt} stmt_if ~>{1 + n} B_if)
      (Heval_else_branch : S' |-{stmt} stmt_else ~>{1 + n} B_else)
      (His_join : is_join B_if B_else B_join) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} B_join
  | E_Reorg n S0 S1 B2 stmt (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt ~>{1 + n} B2) :
      S0 |-{stmt} stmt ~>{1 + n} B2
  (* We perform a single loop iteration, and stop because it does not continue. *)
  | E_Loop_Stop n S body B1
      (eval_body : S |-{stmt} body ~>{1 + n} B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (no_continue : lookup rContinue B1 = None) :
      S |-{stmt} (LOOP {{ body }}) ~>{1 + n} (end_loop B1)
  | E_Loop_Continue n S body B1 S1 B2 Bend
      (eval_body : S |-{stmt} body ~>{1 + n} B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (Hcontinue : lookup rContinue B1 = Some S1)
      (Heval2 : S1 |-{stmt} (LOOP {{ body }}) ~>{n} B2)
      (His_join : is_join (end_loop (delete rContinue B1)) B2 Bend) :
      S |-{stmt} (LOOP {{ body }}) ~>{1 + n} Bend
where "S |-{stmt} stmt ~>{ n } B" := (eval_stmt n stmt S B) : llbc_plus_scope.

open Base

(* A scope is a map from variable names to values *)

let rec eval (exp : Ast.t) (scope : Scope.t) : Ast.Prim.t * Scope.t =
  match exp with
  (* x = 5 *)
  | Declare (Ident var, rhs) ->
      (* Evaluate rhs *)
      let value, scope = eval rhs scope in

      (* Put the result into current scope *)
      let scope = Scope.add scope var value in

      (* Declarations evaluate to () *)
      (PUnit, scope)
  (* x := 5 *)
  | Assign (Ident var, rhs) ->
      (* Evaluate rhs *)
      let value, scope = eval rhs scope in

      (* Mutate the entry in the scope *)
      Scope.update scope var value;

      (* Declarations evaluate to () *)
      (PUnit, scope)
  (* x *)
  | Ident var ->
      (* Lookup var in current scope *)
      (Scope.get scope var, scope)
  (* 5 *)
  (* () *)
  (* + *)
  | EPrim prim ->
      (* Primitives are already evaluated *)
      (prim, scope)
  | App (func, arg) ->
      (* Evaluate function *)
      let f, scope =
        match eval func scope with
        | PFunc f, s -> (f, s)
        | _ -> failwith "argument applied to non-function"
      in

      (* Evaluate arguement *)
      let arg_val, scope = eval arg scope in

      (* Apply *)
      let result = f arg_val in

      (result, scope)
  (* x => x + 1 *)
  | Lam (Ident var, body) ->
      ( PFunc
          (fun arg ->
            (* Add argument to scope *)
            let scope = Scope.add scope var arg in

            (* Evaluate body *)
            let body_val, _ = eval body scope in

            body_val),
        scope )
  | Scope e ->
      (* Evaluates, but discards new scope produced *)
      let result, _ = eval e scope in
      (result, scope)
  | _ -> failwith "type error"

let run s = fst (eval (Parser_.parse s) Scope.init)

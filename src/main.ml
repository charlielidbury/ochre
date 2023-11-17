open Base

(* open Core.Std;; *)

(* ---- AST ---- *)

let f a b = a + b

type primitive =
  | PInt of int
  (* | PBool of bool *)
  | PUnit
  | PFunc of (primitive -> primitive)

(* Primitive for integer addition *)
let pAdd =
  PFunc
    (fun l ->
      PFunc
        (fun r ->
          match (l, r) with
          | PInt l, PInt r -> PInt (l + r)
          | _ -> failwith "Type error"))

(* Primitive for ; *)
let pSeq = PFunc (fun _ -> PFunc (fun r -> r))

(* let pNot = PFunc (fun b -> match b with
   | PBool b -> PBool (not b)
   | _ -> failwith "Type error") *)

type expr =
  | Declare of expr * expr
  | Assign of expr * expr
  | Ident of string
  (* Primitives *)
  | Prim of primitive
  (* Functions *)
  | App of expr * expr
  | Lam of expr * expr
(* Variables *)
(* Mutability *)
(* | Mut of expr *)
(* | Ref of expr *)

let ( <+> ) x y = App (App (Prim pSeq, x), y)
let ( <=> ) x y = Declare (x, y)
let ( <:=> ) x y = Assign (x, y)

(* ---- EVALUATION ---- *)

module Scope = struct
  type t = Scope of (string, primitive, String.comparator_witness) Map.t

  let empty = Scope (Map.empty (module String))

  let add (Scope vars) var value : t =
    match Map.add vars ~key:var ~data:value with
    | Map.(`Ok m) ->
        Stdio.print_endline "hello world";
        Scope m
    | Map.(`Duplicate) -> failwith "already in scope"

  let get (Scope vars) var =
    match Map.find vars var with
    | Some value -> value
    | None -> failwith "variable not found in scope"
end

let empty = Map.empty (module String)

let rec eval (exp : expr) (scope : Scope.t) : primitive * Scope.t =
  match exp with
  (* x = 5 *)
  (* x := 5 *)
  | Declare (Ident var, rhs) | Assign (Ident var, rhs) ->
      (* Evaluate rhs *)
      let value, _ = eval rhs scope in

      (* Put the result into current scope *)
      Stdio.print_string "";
      let scope = Scope.add scope var value in

      (* Declarations evaluate to () *)
      (PUnit, scope)
  (* x *)
  | Ident var ->
      (* Lookup var in current scope *)
      (Scope.get scope var, scope)
  (* 5 *)
  (* () *)
  (* + *)
  | Prim prim ->
      (* Primitives are already evaluated *)
      (prim, scope)
  | App (func, arg) ->
      (* Evaluate function *)
      let f =
        match eval func scope with
        | PFunc f, _ -> f
        | _ -> failwith "argument applied to non-function"
      in

      (* Evaluate arguement *)
      let arg_val, _ = eval arg scope in

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
  | _ -> failwith "unhandled eval case"

(* ---- PROGRAMS ---- *)

(* 5; 6 *)
let example_program = App (App (Prim pSeq, Prim (PInt 5)), Prim (PInt 6))

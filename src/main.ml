open Base

(* open Core.Std;; *)

(* ---- AST ---- *)

let f a b = a + b

module Prim = struct
  type t =
    | PInt of int
    (* | PBool of bool *)
    | PUnit
    | PFunc of (t -> t)

  let equal lhs rhs =
    match (lhs, rhs) with
    | PInt l, PInt r -> l = r
    (* | PBool l, PBool r -> l = r *)
    | PUnit, PUnit -> true
    | _ -> false

  let to_string expr =
    match expr with
    | PInt i -> Int.to_string i
    (* | PBool b -> Bool.to_string b *)
    | PUnit -> "()"
    | PFunc _ -> "<function>"

  (* let pNot = PFunc (fun b -> match b with
     | PBool b -> PBool (not b)
     | _ -> failwith "Type error") *)
end

module Expr = struct
  type t =
    | Declare of t * t
    | Assign of t * t
    | Ident of string
    (* Primitives *)
    | EPrim of Prim.t
    (* Functions *)
    | App of t * t
    | Lam of t * t

  (* Variables *)
  (* Mutability *)
  (* | Mut of t *)
  (* | Ref of t *)

  (* Primitive for integer addition *)
  let pAdd =
    EPrim
      (PFunc
         (fun l ->
           PFunc
             (fun r ->
               match (l, r) with
               | PInt l, PInt r -> PInt (l + r)
               | _ -> failwith "Type error")))

  (* Primitive for ; *)
  let pSeq = EPrim (PFunc (fun _ -> PFunc (fun r -> r)))
  let pInt n = EPrim (PInt n)

  (* Useful constructors. *)
  let ( <+> ) x y = App (App (pSeq, x), y)
  let ( <=> ) x y = Declare (x, y)
  let ( <:=> ) x y = Assign (x, y)
  let ( <$> ) x y = App (x, y)
end

(* ---- EVALUATION ---- *)

module Scope = struct
  type t = Scope of (string, Prim.t, String.comparator_witness) Map.t

  let empty = Scope (Map.empty (module String))
  let equal (Scope lhs) (Scope rhs) = Map.equal Prim.equal lhs rhs

  let add (Scope vars) var value : t =
    match Map.add vars ~key:var ~data:value with
    | Map.(`Ok m) -> Scope m
    | Map.(`Duplicate) -> failwith "already in scope"

  let get (Scope vars) var =
    match Map.find vars var with
    | Some value -> value
    | None -> failwith "variable not found in scope"

  let to_string (Scope vars) =
    "{ "
    ^ (Map.to_alist vars
      |> List.map ~f:(fun (k, v) -> k ^ ": " ^ Prim.to_string v)
      |> String.concat ~sep:"\n")
    ^ " }"
end

let rec eval (exp : Expr.t) (scope : Scope.t) : Prim.t * Scope.t =
  match exp with
  (* x = 5 *)
  (* x := 5 *)
  | Declare (Ident var, rhs) | Assign (Ident var, rhs) ->
      (* Evaluate rhs *)
      let value, _ = eval rhs scope in

      (* Put the result into current scope *)
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
  | _ -> failwith "unhandled eval case"

(* ---- PROGRAMS ---- *)

(* 5; 6 *)
let example_program = Expr.App (App (Expr.pSeq, Expr.pInt 5), EPrim (PInt 6))

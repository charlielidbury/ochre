module Prim = struct
  type t =
    | PInt of int
    (* | PBool of bool *)
    | PUnit
    | PFunc of (t -> t)

  (* Is this whole thing just =? *)
  let equal lhs rhs =
    match (lhs, rhs) with
    | PInt l, PInt r -> l = r
    (* | PBool l, PBool r -> l = r *)
    | PUnit, PUnit -> true
    | PFunc l, PFunc r -> l = r
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

let rec equal lhs rhs =
  match (lhs, rhs) with
  | Declare (l1, l2), Declare (r1, r2) -> equal l1 r1 && equal l2 r2
  | Assign (l1, l2), Assign (r1, r2) -> equal l1 r1 && equal l2 r2
  | Ident l, Ident r -> String.equal l r
  | EPrim l, EPrim r -> Prim.equal l r
  | App (l1, l2), App (r1, r2) -> equal l1 r1 && equal l2 r2
  | Lam (l1, l2), Lam (r1, r2) -> equal l1 r1 && equal l2 r2
  | _ -> false

let is_operator c = String.contains "+-*/;=:>" c

let rec to_string e =
  match e with
  | Declare (l, r) -> Printf.sprintf "%s = %s" (to_string l) (to_string r)
  | Assign (l, r) -> Printf.sprintf "%s := %s" (to_string l) (to_string r)
  | Ident s -> s
  | EPrim p -> Prim.to_string p
  | App (App (Ident ";", l), r) ->
      Printf.sprintf "%s;\n%s" (to_string l) (to_string r)
  | App (App (Ident op, l), r) when String.for_all is_operator op ->
      Printf.sprintf "(%s) %s (%s)" (to_string l) op (to_string r)
  | App (l, r) -> Printf.sprintf "%s %s" (to_string l) (to_string r)
  | Lam (l, r) -> Printf.sprintf "%s => (%s)" (to_string l) (to_string r)

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
let pSeq = Ident ";"

(* let pSeq = EPrim (PFunc (fun _ -> PFunc (fun r -> r))) *)
let pInt n = EPrim (PInt n)
let pFn lam = EPrim (PFunc lam)

(* Useful constructors. *)
let ( <+> ) x y = App (App (pSeq, x), y)
let ( <=> ) x y = Declare (x, y)
let ( <:=> ) x y = Assign (x, y)
let ( <$> ) x y = App (x, y)

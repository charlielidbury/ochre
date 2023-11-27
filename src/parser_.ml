open Base
open Angstrom
open Ast

let ( let>>= ) rhs cont = rhs >>= cont

(* PREDICATES *)
let is_whitespace = function
  | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
  | _ -> false

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false
let is_digit = function '0' .. '9' -> true | _ -> false

let list_to_string e_to_string l =
  "["
  ^ List.fold_right l ~init:"" ~f:(fun e acc -> e_to_string e ^ ", " ^ acc)
  ^ "]"

(* PARSERS *)
let whitespace = take_while is_whitespace
let tok s = whitespace *> string s
let operator = take_while1 is_operator

let integer =
  (* 1 if positive, -1 if negative *)
  let>>= sign = char '-' *> return (-1) <|> return 1 in
  (* At least one digit *)
  let>>= digits = take_while1 is_digit in

  return (sign * Int.of_string digits)

let text_ident =
  map2 (satisfy is_alpha)
    (take_while (fun x -> is_alpha x || is_digit x))
    ~f:(fun c cs -> String.make 1 c ^ cs)

let ident = whitespace *> (operator <|> text_ident)

(* COMBINATORS *)
let parens p = tok "(" *> p <* tok ")"
let max_assoc = 8

type atom =
  (* precedence * left_assoc * (fun lhs rhs -> total) *)
  | Operator of (int * bool * (Ast.t -> Ast.t -> Ast.t))
  | Expr of Ast.t

let rec shunting_yard input op_stack out_stack =
  match (input, op_stack, out_stack) with
  (* Group groups of expressions i.e. (f a) + b *)
  | Expr f :: Expr arg :: input, op_stack, out_stack ->
      (shunting_yard [@tailcall])
        (Expr (App (f, arg)) :: input)
        op_stack out_stack
  (* Expressions go straight to the output stack *)
  | Expr e :: input, op_stack, out_stack ->
      (shunting_yard [@tailcall]) input op_stack (e :: out_stack)
  (* Make space for next atom on operator stack *)
  | ( Operator ((new_prec, new_assoc, _) as new_op) :: input,
      (top_prec, _, top_f) :: op_stack,
      rhs :: lhs :: out_stack )
    when top_prec > new_prec || (top_prec = new_prec && new_assoc) ->
      (shunting_yard [@tailcall]) (Operator new_op :: input) op_stack
        (top_f lhs rhs :: out_stack)
  (* Put incoming operator on operator stack *)
  | Operator op :: input, op_stack, out_stack ->
      (shunting_yard [@tailcall]) input (op :: op_stack) out_stack
  (* Once input empty, evaluate all operators *)
  | [], (_, _, top_f) :: op_stack, rhs :: lhs :: out_stack ->
      (shunting_yard [@tailcall]) [] op_stack (top_f lhs rhs :: out_stack)
  (* Once all operators moved over, done *)
  | [], [], [ result ] -> result
  (* Once input empty, evaluate all operators *)
  | _ -> failwith "shunting yard invalid state"

let expr =
  fix (fun expr ->
      let expr_atom =
        choice
          [
            (* 523 *)
            (integer >>| fun n -> EPrim (PInt n));
            (* (expr) *)
            (parens (option (EPrim PUnit) expr) >>| fun e -> Scope e);
            (* xyz *)
            (text_ident >>| fun x -> Ident x);
          ]
        >>| fun e -> Expr e
      in

      let operator_atom =
        let>>= op = operator in
        let normal lhs rhs = App (App (Ident op, lhs), rhs) in
        return
          (Operator
             (match op with
             | ";" -> (0, true, normal)
             | "=" -> (1, false, fun lhs rhs -> Declare (lhs, rhs))
             | ":=" -> (1, false, fun lhs rhs -> Assign (lhs, rhs))
             | "=>" -> (2, false, fun lhs rhs -> Lam (lhs, rhs))
             | "+" | "-" -> (4, true, normal)
             | "*" | "/" -> (5, true, normal)
             | _ -> failwith ("unknown operator" ^ op)))
      in

      let>>= atoms = many1 (whitespace *> (expr_atom <|> operator_atom)) in

      return (shunting_yard atoms [] []))

let parse s =
  Result.ok_or_failwith (parse_string ~consume:All (expr <* whitespace) s)

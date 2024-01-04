open Base

open Ast

let type_infer context expr =
  match expr with
  | Declare (Ident lhs, rhs) ->
      let ty = type_infer context rhs in
      let context' = Context.add lhs ty context in
      PTUnit
  | Ann (e, ty) ->
      type_check context e ty;
      ty
  | EPrim (PInt _) -> PTInt
  | EPrim PUnit -> PTUnit
  

let type_check context expr ty = failwith "TODO"

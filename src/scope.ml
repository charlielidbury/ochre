open Base

type t = Scope of (string, Ast.Prim.t ref, String.comparator_witness) Map.t

let init =
  Scope
    (Map.of_alist_exn
       (module String)
       [ (";", ref (Ast.Prim.PFunc (fun _ -> PFunc (fun r -> r)))) ])

let equal (Scope lhs) (Scope rhs) =
  Map.equal (fun l r -> Ast.Prim.equal !l !r) lhs rhs

let add (Scope vars) var value : t =
  match Map.add vars ~key:var ~data:(ref value) with
  | Map.(`Ok m) -> Scope m
  | Map.(`Duplicate) -> failwith "already in scope"

let get (Scope vars) var =
  match Map.find vars var with
  | Some value -> !value
  | None -> failwith "variable not found in scope"

let update (Scope vars) var value =
  match Map.find vars var with
  | Some entry -> entry := value
  | None -> failwith "variable not found in scope"

let to_string (Scope vars) =
  "{ "
  ^ (Map.to_alist vars
    |> List.map ~f:(fun (k, v) -> k ^ ": " ^ Ast.Prim.to_string !v)
    |> String.concat ~sep:"\n")
  ^ " }"

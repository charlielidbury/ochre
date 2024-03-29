open Base

type t = Scope of (string, Ast.Prim.t ref, String.comparator_witness) Map.t

let binPFun f =
  Ast.Prim.PFunc
    (fun l ->
      Ast.Prim.PFunc
        (fun r ->
          match (l, r) with
          | Ast.(PInt l, PInt r) -> Ast.Prim.PInt (f l r)
          | _ ->
              failwith
                (Printf.sprintf "type error: %s and/or %s not ints"
                   (Ast.Prim.to_string l) (Ast.Prim.to_string r))))

let init =
  Scope
    (Map.of_alist_exn
       (module String)
       [
         (";", ref (Ast.Prim.PFunc (fun _ -> PFunc (fun r -> r))));
         ("+", ref (binPFun ( + )));
         ("-", ref (binPFun ( - )));
         ("*", ref (binPFun ( * )));
         ("/", ref (binPFun ( / )));
       ])

let equal (Scope lhs) (Scope rhs) =
  Map.equal (fun l r -> Ast.Prim.equal !l !r) lhs rhs

let add (Scope vars) var value : t =
  Scope (Map.set vars ~key:var ~data:(ref value))

let get (Scope vars) var =
  match Map.find vars var with
  | Some value -> !value
  | None -> failwith ("(get) variable not found in scope: " ^ var)

let update (Scope vars) var value =
  match Map.find vars var with
  | Some entry -> entry := value
  | None -> failwith ("(update) variable not found in scope: " ^ var)

let to_string (Scope vars) =
  "{ "
  ^ (Map.to_alist vars
    |> List.map ~f:(fun (k, v) -> k ^ ": " ^ Ast.Prim.to_string !v)
    |> String.concat ~sep:"\n")
  ^ " }"

open Main;;

let _ = QCheck_runner.run_tests [
  QCheck.Test.make
    ~name:"sequence returns rhs"
    QCheck.(pair int int)
    (fun (x, y) ->
      let program = 
        Prim(PInt x) <+>
        Prim(PInt y)
      in

      let (result, _end_state) = eval program Scope.empty in

      match result with
        | (PInt yy) -> y == yy
        | _ -> false
    );
  QCheck.Test.make
    ~name:"declarations add to scope"
    QCheck.(int)
    (fun x ->
      let program =
        Ident "x" <=> Prim(PInt x)
      in

      let scope = Scope.empty in
      let scope = Scope.add scope "x" (PInt x) in

      match eval program Scope.empty with
        | (PUnit, s) -> s == scope
        | _ -> false
    );
  (* QCheck.Test.make
    ~name:"example including declarations"
    QCheck.(pair int int)
    (fun (x, y) ->
      let program =
        (Ident "x" <=> Prim(PInt x)) <+>
        (Ident "y" <=> Prim(PInt y)) <+>
        App(App(Prim pAdd, Ident "x"), Ident "y")
      in

      let (result, _end_state) = eval program Scope.empty in
      
      match result with
        | (PInt yy) -> y == yy
        | _ -> false
    ); *)
]

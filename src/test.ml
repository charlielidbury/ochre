open Main

let _ =
  QCheck_runner.run_tests
    [
      QCheck.Test.make ~name:"sequence returns rhs" ~count:100
        QCheck.(pair int int)
        (fun (x, y) ->
          let program = Expr.(pInt x <+> pInt y) in

          let result, _end_state = eval program Scope.empty in

          match result with PInt yy -> y == yy | _ -> false);
      QCheck.Test.make ~name:"scope acts as map" ~count:100
        QCheck.(int)
        (fun x ->
          let scope = Scope.add Scope.empty "x" (PInt x) in
          let x_back = Scope.get scope "x" in

          match x_back with PInt x_back -> x == x_back | _ -> false);
      QCheck.Test.make ~name:"declarations add to scope" ~count:100
        QCheck.(int)
        (fun x ->
          let program = Expr.(Ident "x" <=> pInt x) in

          let scope = Scope.empty in
          let scope = Scope.add scope "x" (PInt x) in

          match eval program Scope.empty with
          | PUnit, s -> Scope.equal scope s
          | _ -> false);
      QCheck.Test.make ~name:"example including declarations"
        QCheck.(pair int int)
        (fun (x, y) ->
          let program =
            Expr.(
              Ident "x" <=> pInt x
              <+> (Ident "y" <=> pInt y)
              <+> (pAdd <$> Ident "x" <$> Ident "y"))
          in

          let result, _end_state = eval program Scope.empty in

          match result with PInt res -> res == x + y | _ -> false);
      QCheck.Test.make ~name:"declarations dont mutate scope" ~count:100
        QCheck.(int)
        (fun x ->
          let scope_before = Scope.empty in

          let program = Expr.(Ident "x" <=> pInt x) in

          let result, scope_after = eval program scope_before in

          match result with
          | PUnit ->
              (* Must have added x to scope *)
              Scope.equal scope_after (Scope.add Scope.empty "x" (PInt x))
              (* Must not have mutated scope in place *)
              && Scope.equal scope_before Scope.empty
          | _ -> false);
      QCheck.Test.make ~name:"assignments do mutate scope" ~count:100
        QCheck.(int)
        (fun x ->
          let scope_before = Scope.add Scope.empty "x" Prim.PUnit in

          let program = Expr.(Ident "x" <:=> pInt x) in

          let result, _scope_after = eval program scope_before in

          match (result, Scope.get scope_before "x") with
          | PUnit, PInt xx -> xx == x
          | _ -> false);
    ]

let _ =
  QCheck_runner.run_tests
    [
      QCheck.Test.make ~name:"sequence returns rhs" ~count:100
        QCheck.(pair int int)
        (fun (x, y) ->
          let program = Ast.(pInt x <+> pInt y) in

          let result, _end_state = Eval.eval program Scope.init in

          match result with PInt yy -> y == yy | _ -> false);
      QCheck.Test.make ~name:"scope acts as map" ~count:100
        QCheck.(small_int)
        (fun x ->
          let scope = Scope.add Scope.init "x" (PInt x) in
          let x_back = Scope.get scope "x" in

          match x_back with PInt x_back -> x == x_back | _ -> false);
      QCheck.Test.make ~name:"declarations add to scope" ~count:100
        QCheck.(small_int)
        (fun x ->
          let program = Ast.(Ident "x" <=> pInt x) in

          match Eval.eval program Scope.init with
          | PUnit, s -> Scope.get s "x" = PInt x
          | _ -> false);
      QCheck.Test.make ~name:"example including declarations"
        QCheck.(pair small_int small_int)
        (fun (x, y) ->
          let program =
            Ast.(
              Ident "x" <=> pInt x
              <+> (Ident "y" <=> pInt y)
              <+> (pAdd <$> Ident "x" <$> Ident "y"))
          in

          let result, _end_state = Eval.eval program Scope.init in

          match result with PInt res -> res == x + y | _ -> false);
      QCheck.Test.make ~name:"declarations dont mutate scope" ~count:100
        QCheck.(small_int)
        (fun x ->
          let scope_before = Scope.init in

          let program = Ast.(Ident "x" <=> pInt x) in

          let result, scope_after = Eval.eval program scope_before in

          match result with
          | PUnit ->
              (try
                 let _ = Scope.get scope_before "x" in
                 false
               with _ -> true)
              && Scope.get scope_after "x" = PInt x
          | _ -> false);
      QCheck.Test.make ~name:"assignments do mutate scope" ~count:100
        QCheck.(small_int)
        (fun x ->
          let scope_before = Scope.add Scope.init "x" Ast.Prim.PUnit in

          let program = Ast.(Ident "x" <:=> pInt x) in

          let result, _scope_after = Eval.eval program scope_before in

          match (result, Scope.get scope_before "x") with
          | PUnit, PInt xx -> xx == x
          | _ -> false);
      QCheck.Test.make ~name:"lambdas work" ~count:100
        QCheck.(small_int)
        (fun x ->
          let program =
            Ast.(Lam (Ident "x", pAdd <$> Ident "x" <$> pInt 1) <$> pInt x)
          in

          let result, _end_state = Eval.eval program Scope.init in

          match result with PInt res -> res == x + 1 | _ -> false);
      QCheck.Test.make ~name:"mini end to end" ~count:100 QCheck.unit (fun () ->
          let s = "x = 1 + 2; y = x + x; f = a => b => a + b; f x y" in

          let target_result = 9 in

          let e =
            Result.get_ok (Angstrom.parse_string Parser_.expr s ~consume:Prefix)
          in
          let result, _end_state = Eval.eval e Scope.init in

          match result with PInt res -> res == target_result | _ -> false);
      QCheck.Test.make ~name:"scope hides declares" ~count:100 QCheck.unit
        (fun () ->
          let s = "x = 5; (x = 6); x" in

          let target_result = 5 in

          let e =
            Result.get_ok (Angstrom.parse_string Parser_.expr s ~consume:Prefix)
          in
          let result, _end_state = Eval.eval e Scope.init in

          match result with PInt res -> res == target_result | _ -> false);
      QCheck.Test.make ~name:"scope doesn't hide assigns" ~count:100 QCheck.unit
        (fun () ->
          let s = "x = 5; (x := 6); x" in

          let target_result = 6 in

          let e =
            Result.get_ok (Angstrom.parse_string Parser_.expr s ~consume:Prefix)
          in
          let result, _end_state = Eval.eval e Scope.init in

          match result with PInt res -> res == target_result | _ -> false);
    ]

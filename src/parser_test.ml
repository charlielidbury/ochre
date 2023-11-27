let _ =
  QCheck_runner.run_tests
    [
      QCheck.Test.make ~name:"test" ~count:100
        QCheck.(small_signed_int)
        (fun x ->
          let s = string_of_int x in

          match Angstrom.parse_string Parser_.expr s ~consume:Prefix with
          | Result.Ok ast -> Ast.equal ast Ast.(pInt x)
          | Result.Error _ -> false);
      QCheck.Test.make ~name:"test" ~count:100
        QCheck.(pair small_signed_int small_signed_int)
        (fun (x, y) ->
          let s = string_of_int x ^ " - " ^ string_of_int y in

          match Angstrom.parse_string Parser_.expr s ~consume:Prefix with
          | Result.Ok ast -> Ast.equal ast Ast.(Ident "-" <$> pInt x <$> pInt y)
          | Result.Error _ -> false);
      QCheck.Test.make ~name:"double binary op" ~count:1 QCheck.unit (fun () ->
          let s = "1 + 2 + 3" in

          let target_ast =
            Ast.(Ident "+" <$> (Ident "+" <$> pInt 1 <$> pInt 2) <$> pInt 3)
          in

          match Angstrom.parse_string Parser_.expr s ~consume:Prefix with
          | Result.Ok ast -> Ast.equal ast target_ast
          | Result.Error _ -> false);
      QCheck.Test.make ~name:"double lambda" ~count:1 QCheck.unit (fun () ->
          let s = "a => b => a + b" in

          let target_ast =
            Ast.(
              Lam
                ( Ident "a",
                  Lam (Ident "b", Ident "+" <$> Ident "a" <$> Ident "b") ))
          in

          match Angstrom.parse_string Parser_.expr s ~consume:Prefix with
          | Result.Ok ast -> Ast.equal ast target_ast
          | Result.Error _ -> false);
      QCheck.Test.make ~name:"shunting yard" ~count:1 QCheck.unit (fun () ->
          let s = "f a + b" in

          let target_ast =
            Ast.(Ident "+" <$> (Ident "f" <$> Ident "a") <$> Ident "b")
          in

          match Angstrom.parse_string Parser_.expr s ~consume:Prefix with
          | Result.Ok ast -> Ast.equal ast target_ast
          | Result.Error _ -> false);
      QCheck.Test.make ~name:"mini end to end" ~count:1 QCheck.unit (fun () ->
          let s = "x = 1 + 2; y = x + x; f = a => b => a + b; f x y" in

          let target_ast =
            Ast.(
              Ident "x"
              <=> (Ident "+" <$> pInt 1 <$> pInt 2)
              <+> (Ident "y" <=> (Ident "+" <$> Ident "x" <$> Ident "x"))
              <+> (Ident "f"
                  <=> Lam
                        ( Ident "a",
                          Lam (Ident "b", Ident "+" <$> Ident "a" <$> Ident "b")
                        ))
              <+> (Ident "f" <$> Ident "x" <$> Ident "y"))
          in

          match Angstrom.parse_string Parser_.expr s ~consume:All with
          | Result.Ok ast -> Ast.equal ast target_ast
          | Result.Error e -> failwith e);
    ]

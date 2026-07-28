import Dllbc.Uni

open Lean

namespace Dllbc

/-! ## The `decl{ … }` declaration surface -/

declare_syntax_cat declParam
declare_syntax_cat declBody

syntax ident ":" uterm : declParam
syntax "{" ublk "}" : declBody              -- body: the unified grammar in term mode
syntax "=" "%" term : declBody              -- escape hatch: splice a raw `Term` body

syntax "decl{" "fn" ident "(" declParam,* ")" "->" uterm declBody "}" : term
syntax "decl{" "fn" ident "(" declParam,* ")" "->" uterm "back" "=" uterm declBody "}" : term

namespace DeclMacro
open Lean

/-- Shared assembly: build the `Decl` term from its parsed pieces. -/
def assemble (name : Ident) (params : Array (TSyntax `declParam)) (ret : TSyntax `uterm)
    (bk : Option (TSyntax `uterm)) (body : TSyntax `declBody) : MacroM (TSyntax `term) := do
  let parsed ← params.toList.mapM fun (p : TSyntax `declParam) => match p with
    | `(declParam| $x:ident : $τ:uterm) => pure (x.getId.toString, τ)
    | _ => Macro.throwErrorAt p "decl: malformed parameter (expected `x : τ`)"
  let names := parsed.map (·.1)
  let n := names.length
  let fullRctx : List (String × Nat) := names.zip (List.range n)
  let teleSyns ← buildTele [] 0 parsed                      -- each entry sees only earlier params
  let (retT, _) ← elabUTerm true fullRctx [] 0 ret          -- retType (type mode) sees the whole telescope
  let backT ← match bk with
    | some b => do let (bt, _) ← elabUTerm true fullRctx [] 0 b; `(some $bt)
    | none   => `((none : Option Dllbc.Term))
  let bodyT ← match body with                               -- unified `ublk` block, or a `%` splice
    | `(declBody| { $b:ublk }) => do let (t, _) ← elabUBlk false fullRctx [] n b; pure t
    | `(declBody| = % $t:term) => pure ⟨t.raw⟩
    | _ => Macro.throwErrorAt body "decl: malformed body"
  -- `Decl.mk` positionally (name, telescope, retType, body, back): a structure
  -- literal `{ … back := … }` cannot be written here, since declaring the surface
  -- keyword `back` reserves the token, colliding with the field name.
  `(Dllbc.Decl.mk $(quote name.getId.toString) [$teleSyns,*] $retT $bodyT $backT)

end DeclMacro

open DeclMacro in
macro_rules
  | `(decl{ fn $name:ident ( $params,* ) -> $ret:uterm $body:declBody }) =>
    assemble name params.getElems ret none body
  | `(decl{ fn $name:ident ( $params,* ) -> $ret:uterm back = $bk:uterm $body:declBody }) =>
    assemble name params.getElems ret (some bk) body

end Dllbc

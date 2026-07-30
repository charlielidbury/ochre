import Dllbc.Uni

open Lean

namespace Dllbc

/-! ## The `decl{ … }` declaration surface -/

declare_syntax_cat declParam
declare_syntax_cat declBody

syntax ident ":" uterm : declParam
syntax "{" ublk "}" : declBody              -- body: the unified grammar in term mode
syntax "=" "%" term : declBody              -- escape hatch: splice a raw `Term` body

-- §1.2's `[k]`, the decreasing-argument index. Written as the PARAMETER'S NAME
-- (`fn quicksort [fuel] (…)`) and resolved to its positional index here — the
-- kernel wants an index, but a name is what a reader can check. Required of any
-- function that calls itself; see `Decl.dec` and the call rule's guard.
syntax "decl{" "fn" ident ("[" ident "]")? "(" declParam,* ")" "->" uterm declBody "}" : term
syntax "decl{" "fn" ident ("[" ident "]")? "(" declParam,* ")" "->" uterm "back" "=" uterm declBody "}" : term

namespace DeclMacro
open Lean

/-- Shared assembly: build the `Decl` term from its parsed pieces. -/
def assemble (name : Ident) (dec : Option Ident) (params : Array (TSyntax `declParam)) (ret : TSyntax `uterm)
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
  let decT ← match dec with
    | none => `((none : Option Nat))
    | some d =>
      match idxOf? names.reverse d.getId.toString with     -- reverse: idxOf? is innermost-first
      | some i => `(some $(quote (n - 1 - i)))
      | none => Macro.throwErrorAt d s!"decl: decreasing argument '{d.getId}' is not a parameter of '{name.getId}'"
  -- `Decl.mk` positionally (name, telescope, retType, body, back, dec): a structure
  -- literal `{ … back := … }` cannot be written here, since declaring the surface
  -- keyword `back` reserves the token, colliding with the field name.
  `(Dllbc.Decl.mk $(quote name.getId.toString) [$teleSyns,*] $retT $bodyT $backT $decT)

end DeclMacro

open DeclMacro in
macro_rules
  | `(decl{ fn $name:ident $[[$dec:ident]]? ( $params,* ) -> $ret:uterm $body:declBody }) =>
    assemble name dec params.getElems ret none body
  | `(decl{ fn $name:ident $[[$dec:ident]]? ( $params,* ) -> $ret:uterm back = $bk:uterm $body:declBody }) =>
    assemble name dec params.getElems ret (some bk) body

end Dllbc

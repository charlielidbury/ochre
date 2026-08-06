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
-- function that calls itself; see `FnDef.dec` and the call rule's guard.
syntax "decl{" "fn" ident ("[" ident "]")? "(" declParam,* ")" "->" uterm declBody "}" : term
syntax "decl{" "fn" ident ("[" ident "]")? "(" declParam,* ")" "->" uterm "back" "=" uterm declBody "}" : term

namespace DeclMacro
open Lean

/-- Shared assembly: build the `FnDef` term from its parsed pieces. -/
def assemble (name : Ident) (dec : Option Ident) (params : Array (TSyntax `declParam)) (ret : TSyntax `uterm)
    (bk : Option (TSyntax `uterm)) (body : TSyntax `declBody) : MacroM (TSyntax `term) := do
  let parsed ← params.toList.mapM fun (p : TSyntax `declParam) => match p with
    | `(declParam| $x:ident : $τ:uterm) => pure (x.getId.toString, τ)
    | _ => Macro.throwErrorAt p "decl: malformed parameter (expected `x : τ`)"
  let names := parsed.map (·.1)
  let n := names.length
  let fullRctx : List (String × Nat) := names.zip (List.range n)
  let teleSyns ← (buildTele [] 0 parsed).run' {}             -- each entry sees only earlier params
  let (retT, _) ← (elabUTerm true fullRctx [] 0 ret).run' {} -- retType (type mode) sees the whole telescope
  let bodyT ← match body with                               -- unified `ublk` block, or a `%` splice
    | `(declBody| { $b:ublk }) => do let (t, _) ← (elabUBlk false fullRctx [] n b).run' {}; pure t
    | `(declBody| = % $t:term) => pure ⟨t.raw⟩
    | _ => Macro.throwErrorAt body "decl: malformed body"
  let decT ← match dec with
    | none => `((none : Option Nat))
    | some d =>
      match idxOf? names.reverse d.getId.toString with     -- reverse: idxOf? is innermost-first
      | some i => `(some $(quote (n - 1 - i)))
      | none => Macro.throwErrorAt d s!"decl: decreasing argument '{d.getId}' is not a parameter of '{name.getId}'"
  -- `FnDef.mk` positionally (name, telescope, retType, body, dec). It was positional
  -- because the surface once reserved a `back` keyword that collided with the field
  -- name; the keyword and the field retired together in M27-P2, and the positional
  -- form is kept because that is what `progOf`'s round-trips are written against.
  `(Dllbc.FnDef.mk $(quote name.getId.toString) [$teleSyns,*] $retT $bodyT $decT)

end DeclMacro

open DeclMacro in
macro_rules
  | `(decl{ fn $name:ident $[[$dec:ident]]? ( $params,* ) -> $ret:uterm $body:declBody }) =>
    assemble name dec params.getElems ret none body

end Dllbc

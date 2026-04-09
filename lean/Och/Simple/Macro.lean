import Lean
import Och.Simple.Syntax

/-!
# `soch{...}` Macro for Simple Och

Compiles human-readable syntax to de Bruijn `Och.Simple.Expr` at elaboration time.

Bare identifiers resolve as bound variables (de Bruijn index) when in the
binding context, otherwise as Lean-level references.

## Syntax

```
term ::=
  | x                          -- bound variable or Lean-level splice
  | λ(x : term). term          -- lambda
  | μ(x : term). term          -- mu (self-reference)
  | (term : term)              -- ascription
  | term term                  -- application (left-associative)
  | term → term                -- arrow (right-assoc, sugar for λ_:A. B)
  | ⊤                          -- top type
  | (term)                     -- grouping
```
-/

open Lean

-- ============================================================
-- Syntax category
-- ============================================================

declare_syntax_cat soch

syntax:100 ident                                       : soch
syntax:100 "⊤"                                         : soch
syntax:100 "(" soch ":" soch ")"                       : soch
syntax:100 "(" soch ")"                                : soch
syntax:50  soch:50 soch:51                             : soch
syntax:30  soch:31 " → " soch:30                       : soch
syntax:10  "λ" "(" ident ":" soch ")" "." soch:10     : soch
syntax:10  "λ" "(" "_" ":" soch ")" "." soch:10       : soch
syntax:10  "μ" "(" ident ":" soch ")" "." soch:10     : soch

syntax "soch{" soch "}" : term

-- ============================================================
-- Expansion
-- ============================================================

namespace SochMacro

private def findIdx? : List String → String → Option Nat
  | [], _ => none
  | x :: xs, name => if x == name then some 0 else (findIdx? xs name).map (· + 1)

/-- Recursively expand `soch` syntax to `Och.Simple.Expr` constructor calls.
    `ctx` tracks names of enclosing binders (innermost first). -/
partial def expand (ctx : List String) (stx : TSyntax `soch) : MacroM (TSyntax `term) := do
  match stx with
  | `(soch| ⊤) =>
    `(Och.Simple.Expr.top)
  | `(soch| ($a : $b)) =>
    let a' ← expand ctx a; let b' ← expand ctx b
    `(Och.Simple.Expr.asc $a' $b')
  | `(soch| ($a)) =>
    expand ctx a
  | `(soch| $f:soch $a:soch) =>
    let f' ← expand ctx f; let a' ← expand ctx a
    `(Och.Simple.Expr.app $f' $a')
  | `(soch| $a:soch → $b:soch) =>
    let a' ← expand ctx a; let b' ← expand ("_" :: ctx) b
    `(Och.Simple.Expr.lam $a' $b')
  | `(soch| λ ($x:ident : $dom:soch) . $body:soch) =>
    let dom' ← expand ctx dom
    let body' ← expand (x.getId.toString :: ctx) body
    `(Och.Simple.Expr.lam $dom' $body')
  | `(soch| λ (_ : $dom:soch) . $body:soch) =>
    let dom' ← expand ctx dom
    let body' ← expand ("_" :: ctx) body
    `(Och.Simple.Expr.lam $dom' $body')
  | `(soch| μ ($x:ident : $ann:soch) . $body:soch) =>
    let ann' ← expand ctx ann
    let body' ← expand (x.getId.toString :: ctx) body
    `(Och.Simple.Expr.mu $ann' $body')
  | `(soch| $x:ident) =>
    let name := x.getId.toString
    match findIdx? ctx name with
    | some i => `(Och.Simple.Expr.var $(Syntax.mkNumLit (toString i)))
    | none => `($x)
  | _ => Macro.throwError "soch: unexpected syntax"

end SochMacro

macro_rules
  | `(soch{ $body:soch }) => SochMacro.expand [] body

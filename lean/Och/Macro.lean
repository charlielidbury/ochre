import Lean
import Och.Syntax

/-!
# `och{...}` Macro

Compiles human-readable Och syntax to de Bruijn `Expr` at elaboration time.

Bare identifiers resolve as bound variables (de Bruijn index) when in the
binding context, otherwise as Lean-level `Expr` references. Unresolved names
are compile-time errors, eliminating the silent-999 sentinel bug.

## Syntax

```
term ::=
  | x                          -- bound variable or Lean-level splice
  | λx:term. term              -- lambda
  | μx:term. term              -- mu (self-reference)
  | (term : term)              -- ascription
  | term term                  -- application (left-associative)
  | term → term                -- arrow (right-assoc, sugar for λ_:A. B)
  | Type                       -- universe
  | let x : term = term in term  -- let-binding (desugars to (λx:T. body) val)
  | (term)                     -- grouping
```
-/

open Lean

-- ============================================================
-- Syntax category
-- ============================================================

declare_syntax_cat och

syntax:100 ident                                    : och
syntax:100 "Type"                                   : och
syntax:100 "(" och ":" och ")"                      : och
syntax:100 "(" och ")"                              : och
syntax:50  och:50 och:51                            : och
syntax:30  och:31 " → " och:30                      : och
syntax:10  "λ" ident ":" och "." och:10             : och
syntax:10  "λ" "_" ":" och "." och:10               : och
syntax:10  "μ" ident ":" och "." och:10             : och
syntax:10  "let" ident ":" och "=" och "in" och:10  : och

syntax "och{" och "}" : term

-- ============================================================
-- Expansion
-- ============================================================

namespace OchMacro

private def findIdx? : List String → String → Option Nat
  | [], _ => none
  | x :: xs, name => if x == name then some 0 else (findIdx? xs name).map (· + 1)

/-- Recursively expand `och` syntax to `Expr` constructor calls.
    `ctx` tracks names of enclosing binders (innermost first). -/
partial def expand (ctx : List String) (stx : TSyntax `och) : MacroM (TSyntax `term) := do
  match stx with
  | `(och| Type) =>
    `(Expr.type)
  | `(och| ($a : $b)) =>
    let a' ← expand ctx a; let b' ← expand ctx b
    `(Expr.asc $a' $b')
  | `(och| ($a)) =>
    expand ctx a
  | `(och| $f:och $a:och) =>
    let f' ← expand ctx f; let a' ← expand ctx a
    `(Expr.app $f' $a')
  | `(och| $a:och → $b:och) =>
    let a' ← expand ctx a; let b' ← expand ("_" :: ctx) b
    `(Expr.lam $a' $b')
  | `(och| λ $x:ident : $dom:och . $body:och) =>
    let dom' ← expand ctx dom
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.lam $dom' $body')
  | `(och| λ _ : $dom:och . $body:och) =>
    let dom' ← expand ctx dom
    let body' ← expand ("_" :: ctx) body
    `(Expr.lam $dom' $body')
  | `(och| μ $x:ident : $ann:och . $body:och) =>
    let ann' ← expand ctx ann
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.mu $ann' $body')
  | `(och| let $x:ident : $ty:och = $val:och in $body:och) =>
    let ty' ← expand ctx ty; let val' ← expand ctx val
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.app (Expr.lam $ty' $body') $val')
  | `(och| $x:ident) =>
    let name := x.getId.toString
    match findIdx? ctx name with
    | some i => `(Expr.bvar $(Syntax.mkNumLit (toString i)))
    | none => `($x)
  | _ => Macro.throwError "och: unexpected syntax"

end OchMacro

macro_rules
  | `(och{ $body:och }) => OchMacro.expand [] body

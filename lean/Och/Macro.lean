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
  | ιx:term. term              -- iota / self-type binder
  | ιx. term                   --   (annotation-free; defaults to :Type)
  | fix x:term. term           -- recursive binder
  | fix x. term                --   (annotation-free; defaults to :Type)
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
syntax:100 "Bot"                                    : och
syntax:100 "(" och ":" och ")"                      : och
syntax:100 "(" och ")"                              : och
syntax:50  och:50 och:51                            : och
syntax:30  och:31 " → " och:30                      : och
syntax:10  "λ" ident ":" och "." och:10             : och
syntax:10  "λ" "_" ":" och "." och:10               : och
syntax:10  "ι" ident ":" och "." och:10             : och
syntax:10  "ι" ident "." och:10                     : och
syntax:10  "fix" ident ":" och "." och:10           : och
syntax:10  "fix" ident "." och:10                   : och
syntax:10  "let" ident ":" och "=" och "in" och:10  : och
syntax:10  "let" ident "=" och "in" och:10           : och

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
  | `(och| Bot) =>
    `(Expr.bot)
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
  | `(och| ι $x:ident : $ann:och . $body:och) =>
    let ann' ← expand ctx ann
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.iota $ann' $body')
  | `(och| ι $x:ident . $body:och) =>
    -- Annotation-free ι: defaults to `Type`. Constructors using
    -- the very-dependent `P:(self → Type)` encoding don't need
    -- a meaningful annotation (DBool.lean, commit 38d1031).
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.iota Expr.type $body')
  | `(och| fix $x:ident : $ann:och . $body:och) =>
    let ann' ← expand ctx ann
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.fix $ann' $body')
  | `(och| fix $x:ident . $body:och) =>
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.fix Expr.type $body')
  | `(och| let $x:ident : $_ty:och = $val:och in $body:och) =>
    -- Desugar: let x : T = v in body  ⟶  (λx:v. body) v
    -- The domain is the value itself (singleton typing via top rule).
    let val' ← expand ctx val
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.app (Expr.lam $val' $body') $val')
  | `(och| let $x:ident = $val:och in $body:och) =>
    -- Desugar: let x = v in body  ⟶  (λx:v. body) v
    let val' ← expand ctx val
    let body' ← expand (x.getId.toString :: ctx) body
    `(Expr.app (Expr.lam $val' $body') $val')
  | `(och| $x:ident) =>
    let name := x.getId.toString
    match findIdx? ctx name with
    | some i => `(Expr.bvar $(Syntax.mkNumLit (toString i)))
    | none => `($x)
  | _ => Macro.throwError "och: unexpected syntax"

end OchMacro

macro_rules
  | `(och{ $body:och }) => OchMacro.expand [] body

-- Smoke tests: annotation-free ι/fix produce *identical* Exprs
-- to the explicit `:Type` form (so existing encodings can drop
-- the annotation without changing their compiled `Expr`).
example : (och{ ι s. λP:(s → Type). P s })
        = (och{ ι s:Type. λP:(s → Type). P s }) := rfl
example : (och{ fix r. r }) = (och{ fix r:Type. r }) := rfl
example : (och{ ι s. λP:(s → Type). λt:(P s). λf:Type. t })
        = Expr.iota .type
            (.lam (.lam (.bvar 0) .type)
              (.lam (.app (.bvar 0) (.bvar 1))
                (.lam .type (.bvar 1)))) := rfl

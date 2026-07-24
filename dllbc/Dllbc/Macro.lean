import Lean
import Dllbc.Syntax

/-!
# `dllbc{ … }` Macro

Compiles the doc's surface syntax to `Term` at elaboration time, mirroring
`Och/Macro.lean`'s discipline: a binding-context list resolves names to
globally-unique runtime `Var` ids, and an unresolved *lowercase* name is an
elaboration-time error (no silent fallback — the lesson of Och's silent-999
bug). Shadowing mints a fresh id.

## Conventions

  * **Lowercase-initial** identifiers are runtime **variables**; they must be
    bound by an enclosing `let`, else it is an error.
  * **Uppercase-initial** identifiers are **constructors** (`Nil`, `Z`,
    `Cons(a, b)`). A bare uppercase name is a nullary constructor.
  * Numeric literals are sugar for `S (S (… Z))` (`0 = Z`).

## Surface grammar

```
e ::= x | N | C | C(e, …) | &mut e | *e | (e) | ()
b ::= let x = e ; b | e := e ; b | e            -- statements, then a final expression
```

A statement sequence with no meaningful result ends in `()` (unit).
-/

open Lean

namespace Dllbc

-- Expressions and blocks (statement sequences producing a final value).
declare_syntax_cat dlle
declare_syntax_cat dllb

syntax:max ident : dlle
syntax:max num : dlle
syntax:max "(" ")" : dlle                     -- unit
syntax:max "(" dlle ")" : dlle                -- grouping
syntax:max ident "(" dlle,* ")" : dlle        -- constructor application C(a, b)
syntax:70 "&mut" dlle:70 : dlle               -- mutable borrow
syntax:75 "*" dlle:75 : dlle                  -- dereference / peel

syntax "let" ident "=" dlle ";" dllb : dllb   -- declaration
syntax dlle ":=" dlle ";" dllb : dllb         -- assignment
syntax dlle : dllb                            -- final expression

syntax "dllbc{" dllb "}" : term

namespace Macro
open Lean

/-- Whether an identifier starts with an uppercase letter (⇒ constructor). -/
def isUpperInit (s : String) : Bool :=
  match s.data with
  | c :: _ => c.isUpper
  | [] => false

/-- Build the `Term` syntax for the numeral `k` as `S (S (… Z))`. -/
partial def buildNat : Nat → MacroM (TSyntax `term)
  | 0 => `(Dllbc.Term.ctorApp "Z" [])
  | k + 1 => do let inner ← buildNat k; `(Dllbc.Term.ctorApp "S" [$inner])

/-- Expand an expression. Expressions never bind, so no id counter is
    threaded; `ctx` maps in-scope names to their runtime ids. -/
partial def expandE (ctx : List (String × Nat)) (stx : TSyntax `dlle) : MacroM (TSyntax `term) := do
  match stx with
  | `(dlle| ()) => `(Dllbc.Term.unit)
  | `(dlle| ($e:dlle)) => expandE ctx e
  | `(dlle| &mut $e:dlle) => do `(Dllbc.Term.borrow $(← expandE ctx e))
  | `(dlle| *$e:dlle) => do `(Dllbc.Term.deref $(← expandE ctx e))
  | `(dlle| $c:ident ($args,*)) => do
    let name := c.getId.toString
    let args' ← args.getElems.mapM (expandE ctx)
    `(Dllbc.Term.ctorApp $(quote name) [$args',*])
  | `(dlle| $n:num) => buildNat n.getNat
  | `(dlle| $x:ident) => do
    let s := x.getId.toString
    if isUpperInit s then
      `(Dllbc.Term.ctorApp $(quote s) [])
    else
      match ctx.lookup s with
      | some id => `(Dllbc.Term.var ⟨$(quote id), $(quote s)⟩)
      | none => Macro.throwErrorAt x s!"dllbc: unbound variable '{s}' (lowercase names must be let-bound)"
  | _ => Macro.throwErrorAt stx "dllbc: unexpected expression syntax"

/-- Expand a block, threading the fresh-id counter `next` through `let`s. -/
partial def expandB (ctx : List (String × Nat)) (next : Nat) (stx : TSyntax `dllb) : MacroM (TSyntax `term) := do
  match stx with
  | `(dllb| let $x:ident = $e:dlle ; $rest:dllb) => do
    let e' ← expandE ctx e
    let name := x.getId.toString
    let rest' ← expandB ((name, next) :: ctx) (next + 1) rest
    `(Dllbc.Term.letIn ⟨$(quote next), $(quote name)⟩ $e' $rest')
  | `(dllb| $p:dlle := $e:dlle ; $rest:dllb) => do
    let p' ← expandE ctx p
    let e' ← expandE ctx e
    `(Dllbc.Term.assign $p' $e' $(← expandB ctx next rest))
  | `(dllb| $e:dlle) => expandE ctx e
  | _ => Macro.throwErrorAt stx "dllbc: unexpected block syntax"

end Macro

macro_rules
  | `(dllbc{ $b:dllb }) => Dllbc.Macro.expandB [] 0 b

end Dllbc

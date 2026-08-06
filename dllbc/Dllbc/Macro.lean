import Lean
import Dllbc.Syntax

/-!
# `dllbc{ … }` Macro

Compiles the doc's surface syntax to `Term` at elaboration time, mirroring
`Och/Macro.lean`'s discipline: a binding-context list resolves names to
globally-unique runtime `Var` ids, and an unresolved *lowercase* name is an
elaboration-time error (no silent fallback — the lesson of Och's silent-999
bug). Shadowing and every match binder mint fresh ids.

## Conventions (now codified in doc §1.1)

  * **Lowercase-initial** identifiers are runtime **variables**; they must be
    bound by an enclosing `let` or match pattern, else it is an error.
  * **Uppercase-initial** identifiers are **constructors** (`Nil`, `Z`,
    `Cons(a, b)`). A bare uppercase name is a nullary constructor.
  * Numeric literals are sugar for `S (S (… Z))` (`0 = Z`).

## Surface grammar

```
e ::= x | N | C | C(e, …) | &mut e | *e | (e) | () | match x { arm, … }
arm  ::= C => body | C(x, …) => body
body ::= { b } | e
b ::= let x = e ; b | e := e ; b | e ; b | e     -- statements, then a final expression
```

`match` in statement position sequences via `e ; b`. A statement sequence with
no meaningful result ends in `()`.

Because `match` introduces binders, the fresh-id counter is threaded through
*every* expander (not only blocks): each function returns the next free id.
-/

open Lean

namespace Dllbc



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

/-- Resolve a scrutinee/variable identifier to its runtime id, erroring if it
    is a constructor (uppercase) or unbound. -/
def lookupVarId (ctx : List (String × Nat)) (x : Ident) : MacroM Nat := do
  let s := x.getId.toString
  if isUpperInit s then
    Macro.throwErrorAt x s!"dllbc: '{s}' is a constructor, expected a variable"
  match ctx.lookup s with
  | some id => pure id
  | none => Macro.throwErrorAt x s!"dllbc: unbound variable '{s}' (lowercase names must be bound)"

/-- Mint fresh runtime ids for a list of pattern binders, extending `ctx` and
    returning the extended context, the next free id, and the binder `Var`
    syntaxes (in order). -/
partial def mintBinders (ctx : List (String × Nat)) (next : Nat) :
    List Ident → MacroM (List (String × Nat) × Nat × Array (TSyntax `term))
  | [] => pure (ctx, next, #[])
  | b :: bs => do
    let name := b.getId.toString
    let vSyntax ← `((⟨$(quote next), $(quote name)⟩ : Dllbc.Var))
    let (ctx', next', rest) ← mintBinders ((name, next) :: ctx) (next + 1) bs
    pure (ctx', next', #[vSyntax] ++ rest)

-- The `expandE`/`expandB` elaborator for that grammar went with it; the unified
-- `elabUTerm`/`elabUBlk` (Uni.lean) is the only surface elaborator now.

end Macro

-- The `dllbc{ … }` / `dllbc [..] { … }` term surfaces that used to live here
-- are gone: `ublk` (Uni.lean) subsumed this grammar, and ProgMacro.lean now
-- carries the one `dllbc{ … }` macro over it. What remains below is the
-- ELABORATION HELPERS (`expandB`, `mintBinders`, `isUpperInit`, `buildNat`) that
-- the unified elaborator still calls.

end Dllbc

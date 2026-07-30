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

declare_syntax_cat dlle
declare_syntax_cat dllb
declare_syntax_cat dllArm
declare_syntax_cat dllArmBody

syntax:max ident : dlle
syntax:max num : dlle
syntax:max "(" ")" : dlle                     -- unit
syntax:max "(" dlle ")" : dlle                -- grouping
syntax:max ident "(" dlle,* ")" : dlle        -- constructor application C(a, b)
syntax:70 "&mut" dlle:70 : dlle               -- mutable borrow
syntax:75 "*" dlle:75 : dlle                  -- dereference / peel
-- ¶2.1's index and range steps, binding tighter than the peel. No evidence slot
-- here: `dllbc{ }` is the concrete-trace surface, where every bound COMPUTES and
-- ¶3.2's supply route 1 ("conversion alone") applies. Cited evidence needs a pure
-- term, which is the unified `uterm` grammar's business.
syntax:max dlle:max noWs "[" dlle "]" : dlle              -- a[i]
syntax:max dlle:max noWs "[" dlle ";" dlle "]" : dlle     -- a[lo ; cnt]
syntax:max dlle:max noWs "[" dlle ";" ".." "]" : dlle     -- a[lo ; ..]
syntax:max "match" ident "{" dllArm,* "}" : dlle   -- pattern match (§3)
syntax:max "match" ident ":" ident "{" dllArm,* "}" : dlle     -- …with a branch equation (M23)
syntax:max "if" dlle "{" dllb "}" "else" "{" dllb "}" : dlle   -- §12 sugar over a Bool match
syntax:max "if" ident ":" dlle "{" dllb "}" "else" "{" dllb "}" : dlle  -- …with a branch equation

syntax "{" dllb "}" : dllArmBody              -- braced block body
syntax dlle : dllArmBody                      -- bare expression body
syntax ident "=>" dllArmBody : dllArm                 -- nullary pattern
syntax ident "(" ident,* ")" "=>" dllArmBody : dllArm -- applied pattern C(x, y)

syntax "let" ident "=" dlle ";" dllb : dllb   -- declaration
syntax dlle ":=" dlle ";" dllb : dllb         -- assignment
syntax dlle ";" dllb : dllb                   -- expression statement (seq)
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

mutual

/-- Expand an expression, threading the fresh-id counter (needed because a
    `match` expression introduces pattern binders). Returns the term and the
    next free id. -/
partial def expandE (ctx : List (String × Nat)) (next : Nat) (stx : TSyntax `dlle) :
    MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(dlle| ()) => return (← `(Dllbc.Term.unit), next)
  | `(dlle| ($e:dlle)) => expandE ctx next e
  | `(dlle| &mut $e:dlle) => do
    let (e', n) ← expandE ctx next e
    return (← `(Dllbc.Term.borrow $e'), n)
  | `(dlle| *$e:dlle) => do
    let (e', n) ← expandE ctx next e
    return (← `(Dllbc.Term.deref $e'), n)
  | `(dlle| $a:dlle[$i:dlle]) => do
    let (a', n1) ← expandE ctx next a
    let (i', n2) ← expandE ctx n1 i
    return (← `(Dllbc.Term.index $a' $i' none), n2)
  | `(dlle| $a:dlle[$lo:dlle ; ..]) => do
    let (a', n1) ← expandE ctx next a
    let (lo', n2) ← expandE ctx n1 lo
    return (← `(Dllbc.Term.range $a' $lo' none none), n2)
  | `(dlle| $a:dlle[$lo:dlle ; $c:dlle]) => do
    let (a', n1) ← expandE ctx next a
    let (lo', n2) ← expandE ctx n1 lo
    let (c', n3) ← expandE ctx n2 c
    return (← `(Dllbc.Term.range $a' $lo' (some $c') none), n3)
  | `(dlle| $c:ident ($args,*)) => do
    let (args', n) ← expandEList ctx next args.getElems.toList
    let name := c.getId.toString
    -- Uppercase-initial `C(…)` is a constructor application; lowercase `f(…)`
    -- is a call to a declared function (§5.3).
    if isUpperInit name then
      return (← `(Dllbc.Term.ctorApp $(quote name) [$args',*]), n)
    else
      return (← `(Dllbc.Term.call $(quote name) [$args',*]), n)
  | `(dlle| $num:num) => return (← buildNat num.getNat, next)
  | `(dlle| match $x:ident { $arms,* }) => do
    let id ← lookupVarId ctx x
    let (arms', n) ← expandArms ctx next arms.getElems.toList
    return (← `(Dllbc.Term.matchE ⟨$(quote id), $(quote x.getId.toString)⟩ none [$arms',*]), n)
  -- M23: `match h : x { … }` — ONE equation binder for the whole match, in scope
  -- in every arm at that arm's own `Id τ ⟨pre-split x⟩ ⟨ctor⟩` (Lean's `match h :
  -- x with`). The name is DECLARED; without it nothing is bound and nothing minted.
  | `(dlle| match $h:ident : $x:ident { $arms,* }) => do
    let id ← lookupVarId ctx x
    let hName := h.getId.toString
    let (arms', n) ← expandArms ((hName, next) :: ctx) (next + 1) arms.getElems.toList
    return (← `(Dllbc.Term.matchE ⟨$(quote id), $(quote x.getId.toString)⟩
      (some ⟨$(quote next), $(quote hName)⟩) [$arms',*]), n)
  | `(dlle| if $c:dlle { $t:dllb } else { $f:dllb }) => do
    -- Sugar (§12): `if e { t } else { f }` = bind e to a fresh Bool scrutinee,
    -- then `match` it. The condition (e.g. `leb(a, b)`) must be Bool-valued.
    let (c', n1) ← expandE ctx next c
    let scrutId := n1
    let (t', n2) ← expandB ctx (n1 + 1) t
    let (f', n3) ← expandB ctx n2 f
    return (← `(Dllbc.Term.letIn ⟨$(quote scrutId), "__if"⟩ $c'
      (Dllbc.Term.matchE ⟨$(quote scrutId), "__if"⟩ none
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])), n3)
  | `(dlle| if $h:ident : $c:dlle { $t:dllb } else { $f:dllb }) => do
    let (c', n1) ← expandE ctx next c
    let hName := h.getId.toString
    let ctx' := (hName, n1 + 1) :: ctx
    let (t', n2) ← expandB ctx' (n1 + 2) t
    let (f', n3) ← expandB ctx' n2 f
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), "__if"⟩ $c'
      (Dllbc.Term.matchE ⟨$(quote n1), "__if"⟩ (some ⟨$(quote (n1 + 1)), $(quote hName)⟩)
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])), n3)
  | `(dlle| $x:ident) => do
    let s := x.getId.toString
    if isUpperInit s then
      return (← `(Dllbc.Term.ctorApp $(quote s) []), next)
    else
      match ctx.lookup s with
      | some id => return (← `(Dllbc.Term.var ⟨$(quote id), $(quote s)⟩), next)
      | none => Macro.throwErrorAt x s!"dllbc: unbound variable '{s}' (lowercase names must be bound)"
  | _ => Macro.throwErrorAt stx "dllbc: unexpected expression syntax"

/-- Expand a comma-separated list of expressions, threading the counter. -/
partial def expandEList (ctx : List (String × Nat)) (next : Nat) :
    List (TSyntax `dlle) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← expandE ctx next a
    let (rest, n2) ← expandEList ctx n1 as
    pure (#[a'] ++ rest, n2)

/-- Expand the arms of a match, threading the counter (binder ids stay
    globally unique across arms). -/
partial def expandArms (ctx : List (String × Nat)) (next : Nat) :
    List (TSyntax `dllArm) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← expandArm ctx next a
    let (rest, n2) ← expandArms ctx n1 as
    pure (#[a'] ++ rest, n2)

/-- Expand one match arm to a `Branch.mk` term. -/
partial def expandArm (ctx : List (String × Nat)) (next : Nat) (arm : TSyntax `dllArm) :
    MacroM (TSyntax `term × Nat) := do
  match arm with
  | `(dllArm| $c:ident => $body:dllArmBody) => do
    let (body', n) ← expandArmBody ctx next body
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [] $body'), n)
  | `(dllArm| $c:ident ($binders,*) => $body:dllArmBody) => do
    let (ctx', next', binderVars) ← mintBinders ctx next binders.getElems.toList
    let (body', n) ← expandArmBody ctx' next' body
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [$binderVars,*] $body'), n)
  | _ => Macro.throwErrorAt arm "dllbc: unexpected match arm"

/-- Expand an arm body: a braced block `{ b }` or a bare expression. -/
partial def expandArmBody (ctx : List (String × Nat)) (next : Nat) (body : TSyntax `dllArmBody) :
    MacroM (TSyntax `term × Nat) := do
  match body with
  | `(dllArmBody| { $b:dllb }) => expandB ctx next b
  | `(dllArmBody| $e:dlle) => expandE ctx next e
  | _ => Macro.throwErrorAt body "dllbc: unexpected arm body"

/-- Expand a block, threading the fresh-id counter through `let`s and any
    `match` binders in expressions. -/
partial def expandB (ctx : List (String × Nat)) (next : Nat) (stx : TSyntax `dllb) :
    MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(dllb| let $x:ident = $e:dlle ; $rest:dllb) => do
    let (e', n1) ← expandE ctx next e
    let name := x.getId.toString
    let (rest', n2) ← expandB ((name, n1) :: ctx) (n1 + 1) rest
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), $(quote name)⟩ $e' $rest'), n2)
  | `(dllb| $p:dlle := $e:dlle ; $rest:dllb) => do
    let (p', n1) ← expandE ctx next p
    let (e', n2) ← expandE ctx n1 e
    let (rest', n3) ← expandB ctx n2 rest
    return (← `(Dllbc.Term.assign $p' $e' $rest'), n3)
  | `(dllb| $e:dlle ; $rest:dllb) => do
    let (e', n1) ← expandE ctx next e
    let (rest', n2) ← expandB ctx n1 rest
    return (← `(Dllbc.Term.seq $e' $rest'), n2)
  | `(dllb| $e:dlle) => expandE ctx next e
  | _ => Macro.throwErrorAt stx "dllbc: unexpected block syntax"

end

end Macro

macro_rules
  | `(dllbc{ $b:dllb }) => do
    let (t, _) ← Dllbc.Macro.expandB [] 0 b
    return t

/-- `dllbcWith [x, y, …]{ … }` pre-binds the named variables to runtime ids
    `0, 1, …` (in listed order), so a program can reference slots seeded
    directly into Ω (symbolic entries have no surface syntax). Fresh binders
    (let, match patterns) mint ids from `n` onward, never colliding with the
    seeded ids. -/
syntax "dllbcWith" "[" ident,* "]" "{" dllb "}" : term

macro_rules
  | `(dllbcWith [ $names,* ] { $b:dllb }) => do
    let nameList := names.getElems.toList.map (fun nm => nm.getId.toString)
    let ctx := nameList.zip (List.range nameList.length)
    let (t, _) ← Dllbc.Macro.expandB ctx nameList.length b
    return t

end Dllbc

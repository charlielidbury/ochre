import Ochr.Surface

/-!
# The `ochr` command: paper-style programs inside Lean files

```
ochr E1 {
  def AddM (x : &Nat) (y : Nat) : Unit :=
    match *x { Z => *x := y | S p => AddM(&p, y) }
  reject def Bad (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
}
```
defines `E1 : Ochr.Surface.Program`. `def` expects the checker to accept the
definition, `reject def` expects it to be rejected. Calls are saturated and written
`f(a, …)` with no space before the parenthesis; `S t`, `Id A t u`, `Eq A t u` and
`cong f h` are written by juxtaposition.
-/

namespace Ochr.Notation
open Lean Ochr.Surface

declare_syntax_cat ochr_term
declare_syntax_cat ochr_binder
declare_syntax_cat ochr_decl

syntax "(" ident " : " ochr_term ")" : ochr_binder
syntax "(" "_" " : " ochr_term ")" : ochr_binder

syntax:max ident : ochr_term
syntax:max num : ochr_term
syntax:max "(" ")" : ochr_term
syntax:max "(" ochr_term ")" : ochr_term
syntax:max "(" ochr_term ", " ochr_term ")" : ochr_term
syntax:max "(" ochr_term " : " ochr_term ")" : ochr_term
syntax:max "⟨" ochr_term ", " ochr_term "⟩" : ochr_term
syntax:max "⊤" : ochr_term
syntax:max "Prop" : ochr_term
syntax:max "Type" : ochr_term
syntax:max (name := ochrCall) ochr_term:max noWs "(" ochr_term,* ")" : ochr_term
syntax:max (name := ochrProj) ochr_term:max noWs "." noWs num : ochr_term
syntax:max "*" ochr_term:max : ochr_term
syntax:max "&" ochr_term:max : ochr_term
syntax:60 ident (ws ochr_term:max)+ : ochr_term
syntax:35 ochr_term:36 " × " ochr_term:35 : ochr_term
syntax:35 ochr_term:36 " ∧ " ochr_term:35 : ochr_term
syntax:25 ochr_term:26 " → " ochr_term:25 : ochr_term
syntax:20 ochr_term:21 " := " ochr_term:20 : ochr_term
syntax:10 ochr_term:11 "; " ochr_term:10 : ochr_term
syntax:10 "let " ident " = " ochr_term:11 "; " ochr_term:10 : ochr_term
syntax:10 "let " ident " : " ochr_term " = " ochr_term:11 "; " ochr_term:10 : ochr_term
syntax:max "match " ochr_term " { " ident " => " ochr_term:10 " | " ident ident " => " ochr_term:10 " }" : ochr_term
syntax:max "match " ochr_term " { " ident " => " ochr_term:10 " | " ident "_" " => " ochr_term:10 " }" : ochr_term
syntax:10 "Π" ochr_binder+ ". " ochr_term:10 : ochr_term
syntax:10 "λ" ochr_binder+ " : " ochr_term:21 " => " ochr_term:10 : ochr_term
syntax:10 "fix " ident ochr_binder+ " : " ochr_term:21 " := " ochr_term:10 : ochr_term

syntax "def " ident ochr_binder* " : " ochr_term:21 " := " ochr_term : ochr_decl
syntax "reject " "def " ident ochr_binder* " : " ochr_term:21 " := " ochr_term : ochr_decl

syntax (name := ochrProgram) "ochr " ident " { " ochr_decl* " }" : command

def strLit (s : String) : TSyntax `term := quote s

mutual
partial def elabTerm (stx : TSyntax `ochr_term) : MacroM (TSyntax `term) := do
  if stx.raw.getKind == ``ochrCall then
    let f : TSyntax `ochr_term := ⟨stx.raw[0]⟩
    let args := stx.raw[2].getSepArgs.map (⟨·⟩ : Syntax → TSyntax `ochr_term)
    let as ← args.mapM elabTerm
    return ← `(STerm.call $(← elabTerm f) [$as,*])
  if stx.raw.getKind == ``ochrProj then
    let t : TSyntax `ochr_term := ⟨stx.raw[0]⟩
    let i := stx.raw[2].isNatLit?.getD 0
    return ← `(STerm.proj $(quote i) $(← elabTerm t))
  match stx with
  | `(ochr_term| $x:ident) => `(STerm.ident $(strLit x.getId.toString))
  | `(ochr_term| $n:num) => `(STerm.num $n)
  | `(ochr_term| ()) => `(STerm.unitLit)
  | `(ochr_term| ($t)) => elabTerm t
  | `(ochr_term| ($a, $b)) => do `(STerm.pair $(← elabTerm a) $(← elabTerm b))
  | `(ochr_term| ($a : $b)) => do `(STerm.ascribe $(← elabTerm a) $(← elabTerm b))
  | `(ochr_term| ⟨$a, $b⟩) => do `(STerm.andI $(← elabTerm a) $(← elabTerm b))
  | `(ochr_term| ⊤) => `(STerm.top)
  | `(ochr_term| Prop) => `(STerm.sort 0)
  | `(ochr_term| Type) => `(STerm.sort 1)
  | `(ochr_term| *$t) => do `(STerm.deref $(← elabTerm t))
  | `(ochr_term| &$t) => do `(STerm.amp $(← elabTerm t))
  | `(ochr_term| $f:ident $args*) => do
    let as ← args.mapM elabTerm
    `(STerm.app $(strLit f.getId.toString) [$as,*])
  | `(ochr_term| $a × $b) => do `(STerm.prod $(← elabTerm a) $(← elabTerm b))
  | `(ochr_term| $a ∧ $b) => do `(STerm.and $(← elabTerm a) $(← elabTerm b))
  | `(ochr_term| $a → $b) => do `(STerm.arrow $(← elabTerm a) $(← elabTerm b))
  | `(ochr_term| $p := $t) => do `(STerm.assign $(← elabTerm p) $(← elabTerm t))
  | `(ochr_term| $a; $b) => do `(STerm.seq $(← elabTerm a) $(← elabTerm b))
  | `(ochr_term| let $x:ident = $t; $u) => do
    `(STerm.letIn $(strLit x.getId.toString) none $(← elabTerm t) $(← elabTerm u))
  | `(ochr_term| let $x:ident : $A = $t; $u) => do
    `(STerm.letIn $(strLit x.getId.toString) (some $(← elabTerm A)) $(← elabTerm t) $(← elabTerm u))
  | `(ochr_term| match $p { $_z:ident => $tz | $_s:ident $y:ident => $ts }) => do
    `(STerm.matchNat $(← elabTerm p) $(← elabTerm tz) $(strLit y.getId.toString) $(← elabTerm ts))
  | `(ochr_term| match $p { $_z:ident => $tz | $_s:ident _ => $ts }) => do
    `(STerm.matchNat $(← elabTerm p) $(← elabTerm tz) "_" $(← elabTerm ts))
  | `(ochr_term| Π $bs*. $c) => do `(STerm.pi [$(← bs.mapM elabBinder),*] $(← elabTerm c))
  | `(ochr_term| λ $bs* : $r => $b) => do
    `(STerm.fix "_" [$(← bs.mapM elabBinder),*] $(← elabTerm r) $(← elabTerm b))
  | `(ochr_term| fix $f:ident $bs* : $r := $b) => do
    `(STerm.fix $(strLit f.getId.toString) [$(← bs.mapM elabBinder),*] $(← elabTerm r) $(← elabTerm b))
  | _ => Macro.throwErrorAt stx "unsupported ochr term"

partial def elabBinder (stx : TSyntax `ochr_binder) : MacroM (TSyntax `term) := do
  match stx with
  | `(ochr_binder| ($x:ident : $A)) => do `(($(strLit x.getId.toString), $(← elabTerm A)))
  | `(ochr_binder| (_ : $A)) => do `(("_", $(← elabTerm A)))
  | _ => Macro.throwErrorAt stx "unsupported binder"
end

def elabDecl (stx : TSyntax `ochr_decl) : MacroM (TSyntax `term) := do
  match stx with
  | `(ochr_decl| def $f:ident $bs* : $r := $b) => do
    `(({ name := $(strLit f.getId.toString), params := [$(← bs.mapM elabBinder),*],
         ret := $(← elabTerm r), body := $(← elabTerm b), expectAccept := true } : SDecl))
  | `(ochr_decl| reject def $f:ident $bs* : $r := $b) => do
    `(({ name := $(strLit f.getId.toString), params := [$(← bs.mapM elabBinder),*],
         ret := $(← elabTerm r), body := $(← elabTerm b), expectAccept := false } : SDecl))
  | _ => Macro.throwErrorAt stx "unsupported declaration"

macro_rules
  | `(ochr $name:ident { $ds* }) => do
    let decls ← ds.mapM elabDecl
    `(def $name : Ochr.Surface.Program := [$decls,*])

end Ochr.Notation

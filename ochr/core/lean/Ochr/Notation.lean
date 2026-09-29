import Ochr.Surface
import Lean.Elab.Command

/-!
# The `ochr` command: paper-style programs inside Lean files

```
ochr Std {
  def AddM (x : &Nat) (y : Nat) : Unit by x := (
    match *x {
      Z => *x := y,
      S p => AddM(&p, y),
    }
  )
}

ochr Numbers uses Std {
  def Add23 : Id Nat (Add(2, 3)) 5 := refl
  reject def Bad (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
}
```
defines `Std Numbers : Ochr.Surface.Block`. `def` expects the checker to accept the
definition, `reject def` expects it to be rejected. Calls are saturated and written
`f(a, …)` with no space before the parenthesis; `S t`, `Id A t u`, `Eq A t u` and
`cong f h` are written by juxtaposition. Match arms are separated by commas, and a trailing
comma after the last arm is allowed. No term form contains a comma outside brackets, so an
arm's body (`ochr_term:10`) ends at the next top-level comma. Line breaks are whitespace.

`uses A, B` (optional) names blocks, Lean constants made by earlier `ochr` commands (in this
file or an imported one). A block is checked after the declarations its used blocks export,
transitively and each block once: their own declarations that are `def`s (not `reject`) and
are accepted, checked afresh under the same configuration (`Ochr.Test.libOf`). A block's
report and its assertions cover its own declarations only. The names of a block and of the
blocks it uses form one namespace: a clash is an error when the block is elaborated
(`#ochr_check`, which the command expands to, using `Block.clashes`). Every block also
uses the library block `Prelude` (`Ochr/Prelude.lean`) implicitly.
-/

namespace Ochr.Notation
open Lean Ochr.Surface

declare_syntax_cat ochr_term
declare_syntax_cat ochr_binder
declare_syntax_cat ochr_decl
declare_syntax_cat ochr_arm
declare_syntax_cat ochr_patvar
declare_syntax_cat ochr_ctor
declare_syntax_cat ochr_field
declare_syntax_cat ochr_pat

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
syntax:max (name := ochrCtorP0) ident noWs "[" ochr_term,* "]" : ochr_term
syntax:max (name := ochrCtorP) ident noWs "[" ochr_term,* "]" noWs "(" ochr_term,* ")" : ochr_term
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
-- D60: destructuring `let`, sugar for a one-arm match (`⟨…⟩` is And's `Intro`, `(…, …)`
-- Pair's `Mk`); `rewrite h in t`, a typing rule (RULES [Rewrite])
syntax ident : ochr_pat
syntax "_" : ochr_pat
syntax "⟨" ochr_pat,+ "⟩" : ochr_pat
syntax "(" ochr_pat ", " ochr_pat ")" : ochr_pat
syntax:10 (name := ochrLetAnd) "let " "⟨" ochr_pat,+ "⟩" " = " ochr_term:11 "; " ochr_term:10 : ochr_term
syntax:10 (name := ochrLetPair) "let " "(" ochr_pat ", " ochr_pat ")" " = " ochr_term:11 "; " ochr_term:10 : ochr_term
syntax:10 "rewrite " ochr_term:11 " in " ochr_term:10 : ochr_term
syntax:10 "rewrite " "← " ochr_term:11 " in " ochr_term:10 : ochr_term
-- D61: `split f in t`, `split f { C(x̄) => t, … }`: [Split] on the goal's stuck result of `f`
syntax:10 "split " ident " in " ochr_term:10 : ochr_term
syntax:max (name := ochrSplitArms) "split " ident " { " ochr_arm,+,? " }" : ochr_term
syntax ident : ochr_patvar
syntax "_" : ochr_patvar
syntax ident " => " ochr_term:10 : ochr_arm
syntax ident ochr_patvar " => " ochr_term:10 : ochr_arm
syntax ident "(" ochr_patvar,* ")" " => " ochr_term:10 : ochr_arm
-- arms are separated by commas, with an optional trailing comma (as in Rust)
syntax:max (name := ochrMatch) "match " ochr_term " { " ochr_arm,+,? " }" : ochr_term
syntax:max "match " ochr_term " {" "}" : ochr_term      -- no arms (v2.0: on a type with no constructors)
syntax ident " : " ochr_term : ochr_field
syntax ident : ochr_ctor
syntax ident "(" ochr_field,* ")" : ochr_ctor
syntax:10 "Π" ochr_binder+ ". " ochr_term:10 : ochr_term
syntax:10 "λ" ochr_binder+ " : " ochr_term:21 " => " ochr_term:10 : ochr_term
syntax:10 "fix " ident ochr_binder+ " : " ochr_term:21 (" by " ident)? " := " ochr_term:10 : ochr_term

syntax "def " ident ochr_binder* " : " ochr_term:21 (" by " ident)? " := " ochr_term : ochr_decl
syntax "reject " "def " ident ochr_binder* " : " ochr_term:21 (" by " ident)? " := " ochr_term : ochr_decl
syntax "inductive " ident ochr_binder* (" : " ochr_term:21)? (" := " sepBy1(ochr_ctor, " | "))? : ochr_decl
syntax "reject " "inductive " ident ochr_binder* (" : " ochr_term:21)? (" := " sepBy1(ochr_ctor, " | "))? : ochr_decl
syntax "copy " "inductive " ident ochr_binder* (" : " ochr_term:21)? (" := " sepBy1(ochr_ctor, " | "))? : ochr_decl
syntax "reject " "copy " "inductive " ident ochr_binder* (" : " ochr_term:21)? (" := " sepBy1(ochr_ctor, " | "))? : ochr_decl

syntax (name := ochrProgram) "ochr " ident (&" uses " ident,+)? " { " ochr_decl* " }" : command
/-- Report a clash in an `ochr` block's flat namespace (the command `ochr` expands to this). -/
syntax (name := ochrCheck) "#ochr_check " ident : command

def strLit (s : String) : TSyntax `term := quote s

def decOf (d? : Option (TSyntax `ident)) : TSyntax `term :=
  match d? with
  | some d => Syntax.mkApp (mkIdent ``Option.some) #[strLit d.getId.toString]
  | none => mkIdent ``Option.none

mutual
partial def elabTerm (stx : TSyntax `ochr_term) : MacroM (TSyntax `term) := do
  if stx.raw.getKind == ``ochrCall then
    let f : TSyntax `ochr_term := ⟨stx.raw[0]⟩
    let args := stx.raw[2].getSepArgs.map (⟨·⟩ : Syntax → TSyntax `ochr_term)
    let as ← args.mapM elabTerm
    return ← `(STerm.call $(← elabTerm f) [$as,*])
  if stx.raw.getKind == ``ochrCtorP || stx.raw.getKind == ``ochrCtorP0 then
    let c := stx.raw[0].getId.toString
    let ps ← (stx.raw[2].getSepArgs.map (⟨·⟩ : Syntax → TSyntax `ochr_term)).mapM elabTerm
    let as ← if stx.raw.getKind == ``ochrCtorP0 then pure #[] else
      (stx.raw[5].getSepArgs.map (⟨·⟩ : Syntax → TSyntax `ochr_term)).mapM elabTerm
    return ← `(STerm.ctorP $(strLit c) [$ps,*] [$as,*])
  if stx.raw.getKind == ``ochrMatch then
    let p : TSyntax `ochr_term := ⟨stx.raw[1]⟩
    let arms := stx.raw[3].getSepArgs.map (⟨·⟩ : Syntax → TSyntax `ochr_arm)
    let as ← arms.mapM elabArm
    return ← `(STerm.matchGen $(← elabTerm p) [$as,*])
  if stx.raw.getKind == ``ochrLetAnd || stx.raw.getKind == ``ochrLetPair then
    let isAnd := stx.raw.getKind == ``ochrLetAnd
    let scrut : TSyntax `ochr_term := ⟨if isAnd then stx.raw[5] else stx.raw[7]⟩
    let body : TSyntax `ochr_term := ⟨if isAnd then stx.raw[7] else stx.raw[9]⟩
    let b ← elabTerm body
    -- a place is matched as it is (its pattern variables are sub-places); any other
    -- term is bound to a temporary first
    let isPlace := scrut.raw.isIdent || (scrut.raw.getNumArgs == 1 && scrut.raw[0].isIdent) ||
      scrut.raw.getKind == ``ochrProj ||
      (scrut.raw.getNumArgs == 2 && scrut.raw[0].isToken "*")
    let top : Sum (Array (TSyntax `ochr_pat)) (TSyntax `ochr_pat × TSyntax `ochr_pat) :=
      if isAnd then .inl (stx.raw[2].getSepArgs.map (⟨·⟩)) else .inr (⟨stx.raw[2]⟩, ⟨stx.raw[4]⟩)
    let sc ← if isPlace then elabTerm scrut else `(STerm.ident "⋄0")
    let (m, _) ← destructure sc top b 1
    if isPlace then return m
    return ← `(STerm.letIn "⋄0" none $(← elabTerm scrut) $m)
  if stx.raw.getKind == ``ochrSplitArms then
    let f := stx.raw[1].getId.toString
    let arms := stx.raw[3].getSepArgs.map (⟨·⟩ : Syntax → TSyntax `ochr_arm)
    let as ← arms.mapM elabArm
    return ← `(STerm.splitArms $(strLit f) [$as,*])
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
  | `(ochr_term| match $p {}) => do `(STerm.matchGen $(← elabTerm p) [])
  | `(ochr_term| rewrite $h in $t) => do `(STerm.rewrite false $(← elabTerm h) $(← elabTerm t))
  | `(ochr_term| split $f:ident in $t) => do `(STerm.split $(strLit f.getId.toString) $(← elabTerm t))
  | `(ochr_term| rewrite ← $h in $t) => do `(STerm.rewrite true $(← elabTerm h) $(← elabTerm t))
  | `(ochr_term| Π $bs*. $c) => do `(STerm.pi [$(← bs.mapM elabBinder),*] $(← elabTerm c))
  | `(ochr_term| λ $bs* : $r => $b) => do
    `(STerm.fix "_" [$(← bs.mapM elabBinder),*] $(← elabTerm r) none $(← elabTerm b))
  | `(ochr_term| fix $f:ident $bs* : $r $[by $d?]? := $b) => do
    `(STerm.fix $(strLit f.getId.toString) [$(← bs.mapM elabBinder),*] $(← elabTerm r) $(decOf d?) $(← elabTerm b))
  | _ => Macro.throwErrorAt stx "unsupported ochr term"

/-- D60: the one-arm match for a destructuring pattern on `scrut` (an elaborated surface
term, a place), around `body`. `⟨p₁, …, pₙ⟩` is `Intro(p₁, ⟨p₂, …, pₙ⟩)` (right-nested,
n ≥ 2); `(p, q)` is `Mk(p, q)`. A nested pattern gets a fresh name (`⋄k`), matched in
turn. Returns the term and the next fresh index. -/
partial def destructure (scrut : TSyntax `term) (pat : Sum (Array (TSyntax `ochr_pat)) (TSyntax `ochr_pat × TSyntax `ochr_pat))
    (body : TSyntax `term) (k : Nat) : MacroM (TSyntax `term × Nat) := do
  let (ctor, fields) : String × Array (Sum (TSyntax `ochr_pat) (Array (TSyntax `ochr_pat))) ← match pat with
    | .inl ps =>
      if ps.size < 2 then Macro.throwError "a destructuring pattern ⟨…⟩ needs at least two components"
      if ps.size == 2 then pure ("Intro", ps.map .inl)
      else pure ("Intro", #[.inl ps[0]!, .inr (ps.extract 1 ps.size)])
    | .inr (a, b) => pure ("Mk", #[.inl a, .inl b])
  let mut names : Array (TSyntax `term) := #[]
  let mut inner : Array (String × Sum (Array (TSyntax `ochr_pat)) (TSyntax `ochr_pat × TSyntax `ochr_pat)) := #[]
  let mut k := k
  for f in fields do
    match f with
    | .inr rest =>
      let x := s!"⋄{k}"
      k := k + 1
      names := names.push (strLit x)
      inner := inner.push (x, .inl rest)
    | .inl p =>
      match p with
      | `(ochr_pat| $x:ident) => names := names.push (strLit x.getId.toString)
      | `(ochr_pat| _) => names := names.push (strLit "_")
      | `(ochr_pat| ⟨$ps,*⟩) =>
        let x := s!"⋄{k}"
        k := k + 1
        names := names.push (strLit x)
        inner := inner.push (x, .inl ps.getElems)
      | `(ochr_pat| ($a, $b)) =>
        let x := s!"⋄{k}"
        k := k + 1
        names := names.push (strLit x)
        inner := inner.push (x, .inr (a, b))
      | _ => Macro.throwErrorAt p "unsupported destructuring pattern"
  -- the inner matches go around the body, innermost first
  let mut b := body
  for (x, q) in inner.reverse do
    let (m, k') ← destructure (← `(STerm.ident $(strLit x))) q b k
    b := m
    k := k'
  let m ← `(STerm.matchGen $scrut [($(strLit ctor), [$names,*], $b)])
  pure (m, k)

partial def patVar (stx : TSyntax `ochr_patvar) : TSyntax `term :=
  match stx with
  | `(ochr_patvar| $x:ident) => strLit x.getId.toString
  | _ => strLit "_"

partial def elabArm (stx : TSyntax `ochr_arm) : MacroM (TSyntax `term) := do
  match stx with
  | `(ochr_arm| $c:ident => $b) => `(($(strLit c.getId.toString), ([] : List String), $(← elabTerm b)))
  | `(ochr_arm| $c:ident $v:ochr_patvar => $b) =>
    `(($(strLit c.getId.toString), [$(patVar v)], $(← elabTerm b)))
  | `(ochr_arm| $c:ident ( $vs,* ) => $b) =>
    let vs' := vs.getElems.map patVar
    `(($(strLit c.getId.toString), [$vs',*], $(← elabTerm b)))
  | _ => Macro.throwErrorAt stx "unsupported match arm"

partial def elabBinder (stx : TSyntax `ochr_binder) : MacroM (TSyntax `term) := do
  match stx with
  | `(ochr_binder| ($x:ident : $A)) => do `(($(strLit x.getId.toString), $(← elabTerm A)))
  | `(ochr_binder| (_ : $A)) => do `(("_", $(← elabTerm A)))
  | _ => Macro.throwErrorAt stx "unsupported binder"
end

def elabCtor (stx : TSyntax `ochr_ctor) : MacroM (TSyntax `term) := do
  match stx with
  | `(ochr_ctor| $c:ident) => `(($(strLit c.getId.toString), ([] : List (String × STerm))))
  | `(ochr_ctor| $c:ident ( $fs,* )) => do
    let fs' ← fs.getElems.mapM fun f => do
      match f with
      | `(ochr_field| $x:ident : $T) => `(($(strLit x.getId.toString), $(← elabTerm T)))
      | _ => Macro.throwErrorAt f "unsupported field"
    `(($(strLit c.getId.toString), [$fs',*]))
  | _ => Macro.throwErrorAt stx "unsupported constructor"

/-- `inductive D (a : A) … : s := C₁(…) | …` (v2.0): parameters, a sort (default `Type`),
zero or more constructors. -/
def elabInd (n : TSyntax `ident) (bs : Array (TSyntax `ochr_binder)) (s? : Option (TSyntax `ochr_term))
    (cs? : Option (Syntax.TSepArray `ochr_ctor " | ")) (accept : Bool) (isCopy : Bool := false) :
    MacroM (TSyntax `term) := do
  let cs' ← match cs? with
    | some cs => cs.getElems.mapM elabCtor
    | none => pure #[]
  let sort ← match s? with
    | some s => do `(some $(← elabTerm s))
    | none => `(none)
  `(({ name := $(strLit n.getId.toString), params := [], indParams := [$(← bs.mapM elabBinder),*],
       indSort := $sort, ind? := some [$cs',*], indCopy := $(quote isCopy), expectAccept := $(quote accept) } : SDecl))

def elabDecl (stx : TSyntax `ochr_decl) : MacroM (TSyntax `term) := do
  match stx with
  | `(ochr_decl| def $f:ident $bs* : $r $[by $d?]? := $b) => do
    `(({ name := $(strLit f.getId.toString), params := [$(← bs.mapM elabBinder),*],
         ret := $(← elabTerm r), dec := $(decOf d?), body := $(← elabTerm b), expectAccept := true } : SDecl))
  | `(ochr_decl| reject def $f:ident $bs* : $r $[by $d?]? := $b) => do
    `(({ name := $(strLit f.getId.toString), params := [$(← bs.mapM elabBinder),*],
         ret := $(← elabTerm r), dec := $(decOf d?), body := $(← elabTerm b), expectAccept := false } : SDecl))
  | `(ochr_decl| inductive $n:ident $bs* $[: $s?]? $[:= $cs?|*]?) => elabInd n bs s? cs? true
  | `(ochr_decl| reject inductive $n:ident $bs* $[: $s?]? $[:= $cs?|*]?) => elabInd n bs s? cs? false
  | `(ochr_decl| copy inductive $n:ident $bs* $[: $s?]? $[:= $cs?|*]?) => elabInd n bs s? cs? true true
  | `(ochr_decl| reject copy inductive $n:ident $bs* $[: $s?]? $[:= $cs?|*]?) => elabInd n bs s? cs? false true
  | _ => Macro.throwErrorAt stx "unsupported declaration"

macro_rules
  | `(ochr $name:ident $[uses $us,*]? { $ds* }) => do
    let decls ← ds.mapM elabDecl
    let us : Array (TSyntax `term) := match us with
      | some us => us.getElems.map fun u => ⟨u.raw⟩
      | none => #[]
    let defn ← `(def $name : Ochr.Surface.Block :=
      Ochr.Surface.Block.mk $(strLit name.getId.toString) [$us,*] [$decls,*])
    let check ← `(#ochr_check $name)
    return mkNullNode #[defn, check]

open Lean.Elab.Command in
unsafe def evalBlockUnsafe (n : Name) : CommandElabM Block := do
  match (← getEnv).evalConst Block (← getOptions) n with
  | .ok b => pure b
  | .error e => throwError e

open Lean.Elab.Command in
@[implemented_by evalBlockUnsafe]
opaque evalBlock (n : Name) : CommandElabM Block

open Lean.Elab.Command in
elab_rules : command
  | `(#ochr_check $n:ident) => do
    let b ← evalBlock (← liftCoreM (realizeGlobalConstNoOverload n))
    -- every block implicitly uses the library, `Prelude` (v2.1), once it is declared
    let pre ← if b.name == "Prelude" then pure [] else
      try pure [← evalBlock `Prelude] catch _ => pure []
    let cs := b.clashes pre
    unless cs.isEmpty do
      throwErrorAt n m!"ochr {b.name}: {"; ".intercalate cs}"

end Ochr.Notation

import Ochr.Run
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
report covers its own declarations only. The names of a block and of the blocks it uses form
one namespace: a clash is an error. Every block also uses the library block `Prelude`
(`Ochr/Prelude.lean`) implicitly.

The command defines the block and checks it at once, when it is elaborated (`checkBlock`,
docs/07): a rejected `def` is an error at the declaration, and so is an accepted
`reject def`; hovering a declaration's name shows its verdict, the reason for a rejection
included. The checker runs natively: the lakefile precompiles the checker's modules, and
the elaborator calls it (`Ochr.Test.runWith`). `#ochr_check B` checks a block defined
earlier, reporting at `B`.
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
declare_syntax_cat ochr_indmod

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
syntax:max "Type₁" : ochr_term
syntax:max "Type₂" : ochr_term
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

syntax "def " ident ochr_binder* " : " ochr_term:21 (" by " ident)? " := " ochr_term (" implemented " "by " str)? : ochr_decl
syntax "reject " "def " ident ochr_binder* " : " ochr_term:21 (" by " ident)? " := " ochr_term (" implemented " "by " str)? : ochr_decl
-- modifiers of an inductive declaration: `copy` (D53), `abstract` (K3), `unsized` (K2)
syntax "copy " : ochr_indmod
syntax "abstract " : ochr_indmod
syntax "unsized " : ochr_indmod
syntax ochr_indmod* "inductive " ident ochr_binder* (" : " ochr_term:21)? (" := " sepBy1(ochr_ctor, " | "))? : ochr_decl
syntax "reject " ochr_indmod* "inductive " ident ochr_binder* (" : " ochr_term:21)? (" := " sepBy1(ochr_ctor, " | "))? : ochr_decl

syntax (name := ochrProgram) "ochr " ident (&" uses " ident,+)? " { " ochr_decl* " }" : command
/-- Check a block defined earlier, as the `ochr` command does, reporting at the name. -/
syntax (name := ochrCheck) "#ochr_check " ident : command
/-- A test of located errors: declaration `D` of block `B` (defined in this file) is rejected,
and the error is reported at source text `"t"`, or, written `"before⟦t⟧after"`, at the `t`
that is between that context (docs/07). -/
syntax (name := ochrErrorAt) "#ochr_error_at " ident ident str : command

def strLit (s : String) : TSyntax `term := quote s

def implOf (s? : Option (TSyntax `str)) : TSyntax `term :=
  match s? with
  | some s => Syntax.mkApp (mkIdent ``Option.some) #[s]
  | none => mkIdent ``Option.none

def decOf (d? : Option (TSyntax `ident)) : TSyntax `term :=
  match d? with
  | some d => Syntax.mkApp (mkIdent ``Option.some) #[strLit d.getId.toString]
  | none => mkIdent ``Option.none

mutual
/-- A term, wrapped in its source range (`STerm.loc`: located errors and hovers, docs/07).
Parentheses are not a term of their own: `(t)` is `t`, at `t`'s range. -/
partial def elabTerm (stx : TSyntax `ochr_term) : MacroM (TSyntax `term) := do
  let t ← elabTermCore stx
  let paren := stx.raw.getNumArgs == 3 && stx.raw[0].isToken "(" && stx.raw[2].isToken ")"
  match paren, stx.raw.getPos?, stx.raw.getTailPos? with
  | false, some s, some e => `(STerm.loc $(quote s.byteIdx) $(quote e.byteIdx) $t)
  | _, _, _ => pure t

partial def elabTermCore (stx : TSyntax `ochr_term) : MacroM (TSyntax `term) := do
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
  | `(ochr_term| Type₁) => `(STerm.sort 2)
  | `(ochr_term| Type₂) => `(STerm.sort 3)
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
    (cs? : Option (Syntax.TSepArray `ochr_ctor " | ")) (accept : Bool) (mods : Array (TSyntax `ochr_indmod)) :
    MacroM (TSyntax `term) := do
  let has (m : String) : Bool := mods.any fun x => x.raw[0].getAtomVal.trim == m
  let isCopy := has "copy"
  let isAbstract := has "abstract"
  let isUnsized := has "unsized"
  let cs' ← match cs? with
    | some cs => cs.getElems.mapM elabCtor
    | none => pure #[]
  let sort ← match s? with
    | some s => do `(some $(← elabTerm s))
    | none => `(none)
  `(({ name := $(strLit n.getId.toString), params := [], indParams := [$(← bs.mapM elabBinder),*],
       indSort := $sort, ind? := some [$cs',*], indCopy := $(quote isCopy), indAbstract := $(quote isAbstract),
       indUnsized := $(quote isUnsized), expectAccept := $(quote accept) } : SDecl))

def elabDecl (stx : TSyntax `ochr_decl) : MacroM (TSyntax `term) := do
  match stx with
  | `(ochr_decl| def $f:ident $bs* : $r $[by $d?]? := $b $[implemented by $sym?]?) => do
    `(({ name := $(strLit f.getId.toString), params := [$(← bs.mapM elabBinder),*],
         ret := $(← elabTerm r), dec := $(decOf d?), body := $(← elabTerm b), implBy := $(implOf sym?),
         expectAccept := true } : SDecl))
  | `(ochr_decl| reject def $f:ident $bs* : $r $[by $d?]? := $b $[implemented by $sym?]?) => do
    `(({ name := $(strLit f.getId.toString), params := [$(← bs.mapM elabBinder),*],
         ret := $(← elabTerm r), dec := $(decOf d?), body := $(← elabTerm b), implBy := $(implOf sym?),
         expectAccept := false } : SDecl))
  | `(ochr_decl| $ms:ochr_indmod* inductive $n:ident $bs* $[: $s?]? $[:= $cs?|*]?) => elabInd n bs s? cs? true ms
  | `(ochr_decl| reject $ms:ochr_indmod* inductive $n:ident $bs* $[: $s?]? $[:= $cs?|*]?) => elabInd n bs s? cs? false ms
  | _ => Macro.throwErrorAt stx "unsupported declaration"

open Lean.Elab Lean.Elab.Command in
unsafe def evalBlockUnsafe (n : Name) : CommandElabM Block := do
  match (← getEnv).evalConst Block (← getOptions) n with
  | .ok b => pure b
  | .error e => throwError e

open Lean.Elab Lean.Elab.Command in
@[implemented_by evalBlockUnsafe]
opaque evalBlock (n : Name) : CommandElabM Block

open Lean.Elab Lean.Elab.Command in
/-- Text shown on hover over `stx` (a leaf of the info tree whose docstring is `text`, computed
when it is shown). -/
def addHoverLazy (stx : Syntax) (text : Unit → String) : CommandElabM Unit :=
  pushInfoLeaf <| .ofDelabTermInfo {
    elaborator := `Ochr.Notation.ochrProgram, stx, lctx := {}, expectedType? := none,
    expr := mkConst ``Unit.unit, mkDocString? := some fun _ => pure (text ()) }

open Lean.Elab Lean.Elab.Command in
def addHover (stx : Syntax) (text : String) : CommandElabM Unit := addHoverLazy stx fun _ => text

/-- The path a note was made on: its [Split] refinements, oldest first. -/
def pathLabel (refs : List (Nat × Value)) : String :=
  if refs.isEmpty then "before any split" else ", ".intercalate (refs.reverse.map fun (σ, v) => s!"σ{σ} = {v}")

def _root_.Ochr.Note.show : Note → String
  | .value v T ps =>
    let ty := match T with | some T => s!" : {T}" | none => ""
    let lend := if ps.isEmpty then "" else s!", borrowing {", ".intercalate (ps.map (s!"`{·}`"))}"
    s!"`{v}{ty}`{lend}"
  | .goal G => s!"goal `{G}`"
  | .expected A => s!"expected `{A}`"
  | .rule r => r

/-- What a hover over a located term shows: each distinct thing its checks noted (its value
and type, the goal a proof or a split was checked against, the type expected of it as an
argument), labelled by the path's [Split] refinements when there is more than one path. A
goal is left out where the term has a value that is not a proof, and an expected type where
it is the type the term has. -/
def notesText (ns : Array (List (Nat × Value) × Note)) : String := Id.run do
  let data := ns.any fun (_, n) => match n with | .value v _ _ => v != .proof | _ => false
  let types := ns.filterMap fun (_, n) => match n with | .value _ (some T) _ => some (toString T) | _ => none
  let ns := ns.filter fun (_, n) => match n with
    | .goal _ => !data
    | .expected A => !types.contains (toString A)
    | _ => true
  let paths := (ns.map fun (r, _) => pathLabel r).toList.eraseDups
  let mut lines : Array String := #[]
  -- the rules applied here, in the paper's names, one line per path
  for p in paths do
    let rs := (ns.filterMap fun (r, n) => match n with
      | .rule x => if pathLabel r == p then some x else none
      | _ => none).toList.eraseDups
    unless rs.isEmpty do
      lines := lines.push ((if paths.length > 1 then s!"- *{p}*: " else "- ") ++ "rules " ++ " ".intercalate rs)
  for (r, n) in ns.filter (!·.2 matches .rule _) do
    let l := if paths.length > 1 then s!"- *{pathLabel r}*: {n.show}" else s!"- {n.show}"
    unless lines.contains l do lines := lines.push l
  let more := if lines.size > 16 then s!"\n- … {lines.size - 16} more" else ""
  let head := match paths with
    | [p] => if p == pathLabel [] then "" else s!"*where {p}*\n\n"
    | _ => ""
  pure (head ++ "\n".intercalate (lines.extract 0 16).toList ++ more)

/-- The name of a declaration of an `ochr` block (its first identifier). -/
def declName (d : Syntax) : Syntax := (d.getArgs.find? (·.isIdent)).getD d

/-- Syntax standing for a source range of the file (`Loc`), to report or hover at. -/
def locStx (l : Loc) : Syntax := .atom (.synthetic ⟨l.start⟩ ⟨l.stop⟩ true) ""

open Lean.Elab Lean.Elab.Command in
/-- Check block `n` when it is elaborated: the name clashes of its namespace, then every
declaration, with the checker, after the block's library (`Ochr.Test.runWith`, with the
library block `Prelude` once it is declared). `decls` are the declarations' syntax, in
order (empty: every message goes to `ref`). An accepted `def` and a rejected `reject def`
are silent; hovering a declaration's name shows its verdict (a rejection's reason). A
rejected `def` is an error at the declaration, and so is an accepted `reject def`. -/
def checkBlock (n : Name) (ref : Syntax) (decls : Array Syntax) (kw : Syntax := ref) : CommandElabM Unit := do
  let b ← evalBlock n
  -- every block implicitly uses the library, `Prelude` (v2.1), once it is declared
  let pre ← if b.name == "Prelude" then pure none else
    try pure (some (← evalBlock `Prelude)) catch _ => pure none
  let cs := b.clashes pre.toList
  unless cs.isEmpty do
    throwErrorAt ref m!"ochr {b.name}: {"; ".intercalate cs}"
  -- the report is stored before the clock stops, so its (pure) computation is timed; hovering
  -- the `ochr` keyword shows the block's summary
  let out ← IO.mkRef (none : Option Ochr.Test.Report)
  let t0 ← IO.monoNanosNow
  let r := Ochr.Test.runWith pre b.name b (located := true)
  out.set (some r)
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  -- a location outside its declaration's own source would be a wrong underline or hover (a
  -- wrong one is worse than none): such a location is not used
  let inside (i : Nat) (l : Loc) : Bool := match decls[i]? with
    | some d => d.getPos?.any (·.byteIdx ≤ l.start) && d.getTailPos?.any (l.stop ≤ ·.byteIdx)
    | none => false
  -- what each located term noted when it was checked (phase 3), and where a `reject def` is
  -- rejected, one hover per source range
  let mut notes : Std.HashMap (Nat × Nat) (Array (List (Nat × Value) × Note)) := {}
  let mut heads : Std.HashMap (Nat × Nat) String := {}
  for (row, i) in r.rows.zipIdx do
    for e in row.trace do
      if let .note l refs n := e then
        if inside i l then
          notes := notes.insert (l.start, l.stop) ((notes.getD (l.start, l.stop) #[]).push (refs, n))
    if let .rejected m (some l) := row.verdict then
      unless row.expectAccept || !inside i l do
        heads := heads.insert (l.start, l.stop) s!"{row.name} is rejected here, as expected: {m}\n\n"
  for ((a, z), ns) in notes do
    let head := heads.getD (a, z) ""
    addHoverLazy (locStx ⟨a, z⟩) fun _ => head ++ notesText ns
  for ((a, z), head) in heads do
    unless notes.contains (a, z) do addHover (locStx ⟨a, z⟩) head
  addHover kw s!"ochr block {b.name}: {r.passed}/{r.count} declarations as expected ({ms} ms)"
  for (row, i) in r.rows.zipIdx do
    let at_ := match decls[i]? with
      | some d => declName d
      | none => ref
    -- a rejection is reported at the innermost term being checked (phase 2), else at the name
    let verdict := match row.verdict with
      | .rejected m (some l) => if inside i l then row.verdict else .rejected m none
      | v => v
    match verdict, row.expectAccept with
    | .accepted, true => addHover at_ s!"{row.name}: accepted"
    | .accepted, false => logErrorAt at_ m!"{row.name}: expected rejection, but accepted"
    | .rejected m l, true => logErrorAt ((l.map locStx).getD at_) m!"{row.name}: {m}"
    | .rejected m _, false => addHover at_ s!"{row.name}: rejected, as expected: {m}"

open Lean.Elab Lean.Elab.Command in
elab_rules : command
  | `(ochr $name:ident $[uses $us,*]? { $ds* }) => do
    let stx ← getRef
    let decls ← liftMacroM <| ds.mapM elabDecl
    let us : Array (TSyntax `term) := match us with
      | some us => us.getElems.map fun u => ⟨u.raw⟩
      | none => #[]
    -- a block's term nests as deep as its longest sequence, and every term is wrapped in its
    -- location (`STerm.loc`), which doubles that
    elabCommand (← `(set_option maxRecDepth 100000 in def $name : Ochr.Surface.Block :=
      Ochr.Surface.Block.mk $(strLit name.getId.toString) [$us,*] [$decls,*]))
    -- the definition failed (its error is logged): nothing to check
    unless (← getEnv).contains ((← getCurrNamespace) ++ name.getId) do return
    checkBlock (← liftCoreM (realizeGlobalConstNoOverload name)) name (ds.map (·.raw)) stx[0]

open Lean.Elab Lean.Elab.Command in
elab_rules : command
  | `(#ochr_check $n:ident) => do
    checkBlock (← liftCoreM (realizeGlobalConstNoOverload n)) n #[]

open Lean.Elab Lean.Elab.Command in
elab_rules : command
  | `(#ochr_error_at $n:ident $d:ident $t:str) => do
    let b ← evalBlock (← liftCoreM (realizeGlobalConstNoOverload n))
    let pre ← if b.name == "Prelude" then pure none else
      try pure (some (← evalBlock `Prelude)) catch _ => pure none
    let r := Ochr.Test.runWith pre b.name b (located := true)
    match ((r.rows.find? (·.name == d.getId.toString)).map (·.verdict) : Option Verdict) with
    | some (.rejected m (some l)) =>
      let exp := t.getString
      let (pre, mid, post) := match exp.splitOn "⟦" with
        | [a, rest] => match rest.splitOn "⟧" with
          | [b, c] => (a, b, c)
          | _ => ("", exp, "")
        | _ => ("", exp, "")
      let src := (← getFileMap).source
      let got := String.Pos.Raw.extract src ⟨l.start⟩ ⟨l.stop⟩
      let ctx := String.Pos.Raw.extract src ⟨l.start - pre.utf8ByteSize⟩ ⟨l.stop + post.utf8ByteSize⟩
      unless got == mid && ctx == pre ++ mid ++ post do
        throwErrorAt t m!"{d.getId} is rejected at `{got}` (in `{ctx}`), not as expected: {m}"
    | some (.rejected m none) => throwErrorAt d m!"{d.getId} is rejected at no located term: {m}"
    | some .accepted => throwErrorAt d m!"{d.getId} is accepted"
    | none => throwErrorAt d m!"{b.name} has no declaration {d.getId}"

end Ochr.Notation

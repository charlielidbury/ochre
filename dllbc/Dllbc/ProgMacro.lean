import Dllbc.Uni
import Dllbc.Program

open Lean

namespace Dllbc

/-! # `dllbc{ … }` — the one surface (§8), and it checks

A program is a term, so its surface is the term surface: `ublk` in RUNTIME mode.
There is no declaration form to write and nothing for this macro to assemble —
which is the point.

**One macro, because there is one thing to write.** This replaces four spellings
that had all become the same thing:

| was | now |
|---|---|
| `dllbc{ … }` over the old `dllb` grammar | `dllbc{ … }` over `ublk` |
| `dllbcWith [x, y] { … }` | `dllbc [x, y] { … }` |
| `prog{ … }` | `dllbc{ … }` |
| `progWith [f] { … }` | `dllbc [f] from 900 { … }` |

The old `dllb`/`dlle` grammar was the runtime-only ancestor of `ublk`; `ublk`
spans both fragments under the `isTy` flag and produces byte-identical `Term`s on
the runtime subset, so the older grammar had nothing left to say. `pure{ … }` is
this same grammar with `isTy := true` — a `let` there is a β-redex rather than a
slot — and stays a separate spelling only because the arrow it elaborates under
is the other one.

## It is an elaborator, not a macro, and that is the whole diagnostic story

A macro is syntax-to-syntax, so the `Term` does not exist while it runs and the
checker can only be invoked later, from an `#eval` or a `native_decide` that has
no idea where the offending statement was written. This elaborator has the value:
it evaluates the assembled `Term`, walks it with `checkProgramDiag` right there,
and throws the rejection **at the offending syntax** — the argument, the
statement, the arm. A DLLBC error becomes a red squiggle in the editor and a
`file:line:col` error in `lake build`, like every other Lean error.

**What is checked, and why the default is the walk alone.** `checkProgram` is a
⇒-walk plus an audit of each path's result at a return type, and only the audit
needs that type. A bare `dllbc{ … }` does not say what it returns, so it gets the
walk: every rejection the walk raises — moves, borrows, argument types, calls —
is caught and localized, and the audit is left to whoever states a type. Write
`dllbc -> τ { … }` to get both. The surface asks for nothing it does not need:
the errors that are about *statements* need no return type to find.

`dllbc defer_check { … }` opts out entirely, for the programs that exist BECAUSE
they fail — a `progRejects` twin's rejection is the assertion, and failing to
elaborate would delete the test rather than make it.

## Pre-bound names, and why the base is sometimes written

`dllbc [x, y] { … }` binds the listed names to runtime ids `0, 1, …` before the
block starts, for programs that reference slots seeded directly into Ω (symbolic
entries have no surface syntax, so a test seeds them and names them here). Fresh
binders mint ids from there on and never collide.

`from k` moves that base. Its one client is a hand-written caller for a program
`FnMacro.progOf` assembled: `progOf` binds its callees at `progBase` (900) to
stay clear of the ids the assembled bodies already carry, and a caller that wants
to call one has to agree with it. The base is written at the call site rather
than inferred because the two conventions answer to different things — a seeded Ω
on one side, `progBase` on the other — and a surface that silently picked one
would be wrong half the time.
-/

syntax "dllbc{" ublk "}" : term
syntax "dllbc" (&"defer_check")? ("[" ident,* "]")? ("from" num)? ("->" uterm)? "{" ublk "}" : term

namespace DllbcElab
open Lean Elab Term Meta DeclMacro

instance : Inhabited Dllbc.Term := ⟨.unit⟩

/-- Evaluate the assembled expression to a `Term` **value**. The `unsafe` is the
    standard reflective-elaborator one, contained in this function, and the value
    it produces is immediately handed to the very checker it feeds. -/
unsafe def evalTermUnsafe (e : Expr) : TermElabM Dllbc.Term :=
  Meta.evalExpr' Dllbc.Term ``Dllbc.Term e

@[implemented_by evalTermUnsafe]
opaque evalTermValue (e : Expr) : TermElabM Dllbc.Term

/-- Evaluate a list of key terms. Only ever called on the failure path — a
    program that checks pays nothing for its span table. -/
unsafe def evalKeysUnsafe (e : Expr) : TermElabM (List Dllbc.Term) :=
  Meta.evalExpr (List Dllbc.Term) (mkApp (mkConst ``List [levelZero]) (mkConst ``Dllbc.Term)) e

@[implemented_by evalKeysUnsafe]
opaque evalKeysValue (e : Expr) : TermElabM (List Dllbc.Term)

/-- `set_option trace.Dllbc.check true` reports, per program, the wall time spent
    reifying the value and the wall time spent checking. -/
initialize registerTraceClass `Dllbc.check

/-- Run a walker action to an `Expr`, keeping its span table. -/
def elabWith (act : UM (TSyntax `term)) : TermElabM (Expr × SpanAcc) := do
  let (stx, spans) ← liftMacroM (StateT.run act {})
  let e ← elabTerm stx (some (mkConst ``Dllbc.Term))
  synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars e, spans)

/-- Reify accumulated key syntaxes into key **values**, to match a breadcrumb. -/
def keyValues (keys : Array Syntax) : TermElabM (List Dllbc.Term) := do
  let elems : Array (TSyntax `term) := keys.map fun k => ⟨k⟩
  let e ← elabTerm (← `(([$elems,*] : List Dllbc.Term)))
    (some (mkApp (mkConst ``List [levelZero]) (mkConst ``Dllbc.Term)))
  synthesizeSyntheticMVarsNoPostponing
  evalKeysValue (← instantiateMVars e)

/-- The span a breadcrumb key was written at. `none` when the key is not in the
    table (report it, never guess); ambiguity — the same term written twice —
    resolves to the first occurrence and says so. -/
def spanFor (entries : Array (Syntax × Syntax)) (keys : List Dllbc.Term) (crumb : Dllbc.Term) :
    Option (Syntax × Bool) :=
  match keys.findIdx? (· == crumb) with
  | none => none
  | some i =>
    let dup := (keys.filter (· == crumb)).length > 1
    match entries[i]? with
    | some (_, ref) => some (ref, dup)
    | none => none

/-- `x ⇒ Cons, n ⇒ S` — which arms this path took, outermost first. -/
def trailText (trail : List (String × String)) : String :=
  ", ".intercalate (trail.reverse.map fun p => s!"{p.1} ⇒ {p.2}")

/-- Report a rejection at the narrowest syntax the breadcrumb identifies: the
    offending call argument, else the statement, else the return type for an
    audit rejection, else the program itself. -/
def throwDiag {α : Type} (ref : Syntax) (retRef : Option Syntax) (spans : SpanAcc)
    (diag : Diag) : TermElabM α := do
  let path := if diag.trail.isEmpty then m!"" else m!", on the path where {trailText diag.trail}"
  let head := m!"dllbc: the program is rejected{path}:\n{diag.msg}"
  if diag.atReturn then
    if let some r := retRef then throwErrorAt r head
  let find (entries : Array (Syntax × Syntax)) (crumb : Option Dllbc.Term) :
      TermElabM (Option (Syntax × Bool)) := do
    match crumb with
    | none => pure none
    | some c => pure (spanFor entries (← keyValues (entries.map (·.1))) c)
  -- The argument is narrower than the statement it sits in, so it wins.
  let hit ← do
    match ← find spans.args diag.argKey with
    | some h => pure (some h)
    | none => find spans.stmts diag.stmtKey
  match hit with
  | some (r, dup) =>
    let note := if dup then m!"\n(this expression is written more than once in the program; \
      the position shown is its first occurrence)" else m!""
    throwErrorAt r (head ++ note)
  | none => throwErrorAt ref (head ++ m!"\n(no span for the failing statement — reported at the \
      program; this is a span-table gap, please report it)")

/-- Elaborate a program and — unless `defer_check` was written — check it, with
    the audit included exactly when a return type was written. -/
def elabProgram (deferred : Bool) (ref : Syntax) (ret : Option (TSyntax `uterm))
    (act : UM (TSyntax `term)) : TermElabM Expr := do
  let (e, spans) ← elabWith act
  if deferred then return e
  if e.hasMVar || e.hasFVar then
    throwErrorAt ref m!"dllbc: this program cannot be checked at elaboration time — its \
      assembled value is not closed (it mentions a local or an unsolved metavariable). \
      Write `dllbc defer_check \{ … }` if the check must happen elsewhere."
  let retVal ← ret.mapM fun r => do
    let (re, _) ← elabWith (do let (t, _) ← elabUTerm true [] [] 0 r; pure t)
    evalTermValue re
  let t0 ← IO.monoMsNow
  let v ← evalTermValue e
  let t1 ← IO.monoMsNow
  let res := checkProgramDiag v retVal
  let t2 ← IO.monoMsNow
  trace[Dllbc.check] "program: reify {t1 - t0}ms, check {t2 - t1}ms"
  match res with
  | .ok _ => return e
  | .error diag => throwDiag ref (ret.map (·.raw)) spans diag

end DllbcElab

open DeclMacro DllbcElab in
elab_rules : term
  | `(dllbc{ $b:ublk }) =>
    elabProgram false b none (do let (t, _) ← elabUBlk false [] [] 0 b; pure t)
  | `(dllbc $[defer_check%$dc]? $[[ $xs,* ]]? $[from $base]? $[-> $ret]? { $b:ublk }) => do
    let k := (base.map (·.getNat)).getD 0
    let names := (xs.map (·.getElems)).getD #[]
    let rctx := names.toList.enum.map (fun p => (p.2.getId.toString, k + p.1))
    -- A program with PRE-BOUND NAMES is a fragment, not a program: it references
    -- slots something else seeds (a hand-built Ω, or the callees `progOf` bound),
    -- and the elaborator has no Ω to check it against — every such name would be
    -- "not an entry of Ω". So the pre-bound form is unchecked by construction,
    -- which is the honest reading of what writing `[x, y]` means.
    elabProgram (dc.isSome || !names.isEmpty) b ret
      (do let (t, _) ← elabUBlk false rctx [] (k + names.size) b; pure t)

end Dllbc

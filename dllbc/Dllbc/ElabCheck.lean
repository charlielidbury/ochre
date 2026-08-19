import Dllbc.Program

open Lean

namespace Dllbc

/-! # `prog check { … }` — the check happens AS IT ELABORATES (docs/05)

A macro is syntax-to-syntax, so the `Term` does not exist while it runs and the
checker can only be invoked later, from a `native_decide` that has no idea where
the offending statement was written. `prog check { … }` is an *elaborator*: it has
the value, so it evaluates the assembled `Term`, walks it with `checkProgramDiag`
right there, and throws the rejection **at the offending syntax** — the argument,
the statement, the arm. A DLLBC error becomes a red squiggle in the editor and a
`file:line:col` error in `lake build`, like every other Lean error.

## Why the check is OPT-IN, when the plan doc has it as the default

The plan was written when `prog{ }` meant "a program" and `pure{ }` meant "a
term". M29 γ merged them: that brace now delimits an ARBITRARY TERM, and — in its
own header's words — "a term's fragment is not a property of where it was
WRITTEN, it is a property of which arrow CONSUMES it". Most of the ~1700 `prog{ }`
sites in this corpus are types and proof terms (`StdLemmas` alone is 450 of them),
and `checkProgram` has no business ⇒-walking a `Π`. So the brace cannot say
"check me". The word `check` says it, and it is the only thing that does.

This is the one place the port deviates from the reference implementation's
surface decision, and the deviation is forced: at the reference's commit the
checking brace and the pure brace were still two different spellings, so the
brace itself carried the information that `check` now has to carry.

## The walk is the default; the audit needs a type

`checkProgram` is a ⇒-walk plus an audit of each path's result at a return type,
and only the audit needs that type. `prog check { … }` does not say what it
returns, so it gets the walk — which is where moves, borrows, argument types and
calls are rejected, i.e. essentially all of what these spans localize.
`prog check -> τ { … }` gets both. The surface asks for nothing it does not need.

## Splices defer AUTOMATICALLY, and the test is semantic

A block containing `%e` for a Lean-level `Term` *parameter* — the twin-template
pattern, where one body is shared and the return types are spliced so that lying
twins share the body verbatim — assembles to an `Expr` with a free variable in
it. There is no closed value to evaluate and therefore no check to run. That is
not a limitation being worked around: such a template is inherently checked at
each INSTANTIATION (each gets its own `progOk`/`progRejects`, some expecting
rejection), which is the point of writing one. The elaborator asks the assembled
`Expr` whether it is closed and, when it is not, silently declines with a
`trace.Dllbc.check` line saying so.

Asking the `Expr` rather than scanning the syntax for `%` is the better test in
both directions: it catches unsolved metavariables, which no syntactic scan
could, and it does NOT defer a splice of a global constant (`%SwapL`), which has
no free variable and checks perfectly well.

The framing is the object language's own. Elaboration-time checking fires exactly
when the program is comptime-known — the meta level mirroring the object level's
⇝/⇒, and the test suite's own comptime/runtime staging split.

## A note on graceful degradation under splicing (the natural S2.5)

The span table is keyed by STATEMENT TERM, not by path or by byte offset, so it
degrades gracefully rather than going wrong: a template's non-spliced statements
still have valid keys, and only the spliced ones would fall back to the header.
A future instantiation-site check could therefore still localize an error to the
template statement that caused it. Not built here; filed as the natural next
step. -/

syntax "prog" &"check" ("->" uterm)? "{" ublk "}" : term

namespace ProgElab
open Lean Elab Term Meta Dllbc.Surface

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
  Meta.evalExpr (List Dllbc.Term)
    (mkApp (mkConst ``List [levelZero]) (mkConst ``Dllbc.Term)) e

@[implemented_by evalKeysUnsafe]
opaque evalKeysValue (e : Expr) : TermElabM (List Dllbc.Term)

/-- `set_option trace.Dllbc.check true` reports, per program, the wall time spent
    reifying the value and the wall time spent checking — and says so when a
    program was declined rather than checked. -/
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
    table (report it, never guess); ambiguity — the same statement written twice
    — resolves to the first occurrence and says so. -/
def spanFor (norm : Dllbc.Term → Dllbc.Term) (entries : Array (Syntax × Syntax))
    (keys : List Dllbc.Term) (crumb : Dllbc.Term) : Option (Syntax × Bool) :=
  -- Statement keys are normalized HERE rather than in the emitted key (see
  -- `Uni.spanOfStmt`): this is the first module that can name `stmtKeyOf`.
  -- ARGUMENT keys are not normalized at all — an argument is an expression, and
  -- an argument that happens to be a `match` is not a statement whose
  -- continuation should be dropped.
  let keys := keys.map norm
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
  let find (norm : Dllbc.Term → Dllbc.Term) (entries : Array (Syntax × Syntax))
      (crumb : Option Dllbc.Term) : TermElabM (Option (Syntax × Bool)) := do
    match crumb with
    | none => pure none
    | some c => pure (spanFor norm entries (← keyValues (entries.map (·.1))) c)
  -- The argument is narrower than the statement it sits in, so it wins.
  let hit ← do
    match ← find id spans.args diag.argKey with
    | some h => pure (some h)
    | none => find Dllbc.stmtKeyOf spans.stmts diag.stmtKey
  match hit with
  | some (r, dup) =>
    let note := if dup then m!"\n(this statement is written more than once in the program; \
      the position shown is its first occurrence)" else m!""
    throwErrorAt r (head ++ note)
  | none => throwErrorAt ref (head ++ m!"\n(no span for the failing statement — reported at the \
      program; this is a span-table gap, please report it)")

/-- Elaborate a program and check it, with the audit included exactly when a
    return type was written. A program whose assembled value is not closed — a
    spliced template — is declined silently: there is nothing to evaluate, and
    such a template is checked at its instantiations by construction. -/
def elabChecked (ref : Syntax) (ret : Option (TSyntax `uterm))
    (act : UM (TSyntax `term)) : TermElabM Expr := do
  let (e, spans) ← elabWith act
  -- The RETURN TYPE is assembled before the closedness test, and is part of what
  -- that test is asked about. `prog check -> %ret { … }` — the twin-template
  -- shape, where the body is shared and only the type varies per instantiation —
  -- has a perfectly closed BODY and an open type, so testing the body alone
  -- would send an open `Expr` to `evalExpr` and take the kernel's
  -- "declaration has free variables" instead of deferring. Found the hard way.
  let retE ← ret.mapM fun r => do
    let (re, _) ← elabWith (do let (t, _) ← elabUTerm [] [] 0 r; pure t)
    pure re
  let isOpen (x : Expr) : Bool := x.hasMVar || x.hasFVar
  if isOpen e || (retE.map isOpen).getD false then
    trace[Dllbc.check] "program: DEFERRED — the assembled value is not closed (a \
      splice of a local, or an unsolved metavariable). It is checked where it is \
      instantiated."
    return e
  let retVal ← retE.mapM evalTermValue
  let t0 ← IO.monoMsNow
  let v ← evalTermValue e
  let t1 ← IO.monoMsNow
  let res := checkProgramDiag v retVal
  let t2 ← IO.monoMsNow
  trace[Dllbc.check] "program: reify {t1 - t0}ms, check {t2 - t1}ms"
  match res with
  | .ok _ => return e
  | .error diag => throwDiag ref (ret.map (·.raw)) spans diag

end ProgElab

open Surface ProgElab in
elab_rules : term
  | `(prog check $[-> $ret]? { $b:ublk }) =>
    elabChecked b ret (do let (t, _) ← elabUBlk [] [] 0 b; pure t)

end Dllbc

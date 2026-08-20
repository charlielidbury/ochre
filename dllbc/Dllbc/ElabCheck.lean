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

/-! ## The surface, and why `prog{ }` lives HERE rather than beside `ty{ }`

**`prog{ }` checks by default** (M35, the information rule). There is no `check`
word to write: a block whose content is a program gets the ⇒-walk, a block with a
`-> τ` gets the checker that type asks for, and a bare pure term gets nothing
because there is nothing to ask. The annotation moves onto the blocks that must
NOT be checked, which is the smaller set — measured, 107 against 209.

**The dependency shape is forced and is the right one anyway.** The checker
(`checkProgramDiag`) lives in `Program.lean`, so an elaborator that calls it
cannot be declared below `Program` — and `prog{ }` was, because `Machine`, `Pure`,
`Std` and `Program` itself write blocks in it. Those sites are now `ty{ }`
(`ProgMacro`, unchanged and non-checking), which reads better than `prog{ }` ever
did for what they are: bare type expressions like `ty{ Array %m %t }`, `ty{ Unit }`.
Nothing below this file writes a program.

Counted after the move rather than before it: **57 code sites** — `Machine` 31,
`Std` 13, `Pure` 7, `Program` 4, `ProgMacro` 2 — plus 22 prose mentions in
`Uni`, `Syntax`, `FnMacro` and the headers of the above. The port's planning
figure was 26, and it was an undercount: it counted DEFINITIONS that contain a
block rather than blocks, which diverges most in `Machine`, where a single
`hasTypeT` line can nest two (`ty{ Array %(ty{ … }) %t }`).

`StdLemmas` imports this file, so the checking `prog{ }` reaches most of the
corpus transitively (its own 450 blocks are pure and check nothing).

**FORGETTING THE IMPORT IS A PARSE ERROR, NOT A SILENT SKIP — and the reason is
that the SYNTAX moved, not just the elaborator.** An earlier draft of this
paragraph claimed the opposite: that a module missing the import "would get the
LOW-level brace silently", the forgot-the-import-silently-unchecked failure mode,
and that routing through `StdLemmas` was what made forgetting it impossible. That
is wrong, and the build said so. `prog{` is declared HERE and nowhere else —
`ProgMacro` declares `ty{` — so a module that cannot see this file has no `prog{`
token at all and reports `unknown identifier 'prog'`. There is no low-level brace
left for it to fall back to.

This is the stronger guarantee and it is worth having deliberately: the failure
mode the transitive-import argument was constructed to avoid cannot occur,
because the two braces are different tokens rather than the same token with two
meanings. **The transitive-import argument was also empirically false**: four of
the 22 test modules (`Diff`, `Boundaries`, `Traces`, `Ledger`) never imported
`StdLemmas` at all. They now import this file directly, and each is self-
sufficient rather than inheriting from a neighbour — because inheriting is the
fragility, not the fix.

**INVARIANT, and it must survive any future move of this syntax.** Declaring
`prog` as a leading atom makes it a RESERVED TOKEN: `prog` can no longer be an
identifier anywhere downstream of this file. The corpus has no such identifier
today (checked), and the `defer_check`/`->` forms below are written so the
reservation is not widened — `defer_check` is `&"defer_check"`, a non-reserved
keyword, so it stays usable as an identifier. If a future placement threatens
this, stop and report rather than widening it. -/

syntax "prog{" ublk "}" : term
syntax "prog" &"defer_check" "{" ublk "}" : term
syntax "prog" "->" uterm "{" ublk "}" : term

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

/-- Run a walker action to an `Expr`, collecting spans only if asked.

    `collect := false` is the normal path and is what makes the passing case free
    (see `SpanAcc.collect`): the walker's span-filing calls become a boolean test
    and the emitted `Term` is byte-identical. The failing path re-runs the same
    action with `collect := true` to build the table it now needs. -/
def elabWith (collect : Bool) (act : UM (TSyntax `term)) : TermElabM (Expr × SpanAcc) := do
  let (stx, spans) ← liftMacroM (StateT.run act { collect })
  let e ← elabTerm stx (some (mkConst ``Dllbc.Term))
  synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars e, spans)

/-- Elaborate a block and check NOTHING — the fence. Same value as `prog{ }`
    produces, without the check that would reject it. -/
def elabUnchecked (act : UM (TSyntax `term)) : TermElabM Expr := do
  let (e, _) ← elabWith false act
  return e

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
  let head := m!"dllbc{path}:\n{diag.msg}"
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
  | none =>
    -- NO BREADCRUMB AT ALL versus A BREADCRUMB THAT DID NOT MATCH. Only the
    -- second is a defect. The pure check (`checkPureDiag`) raises no breadcrumb
    -- by construction — `hasTypeT` answers `false` without locating anything, so
    -- there is no statement to have a span for — and telling the author to report
    -- a span-table gap for it would be sending them after a bug that is not
    -- there. That case reports at the ascription, which is the thing the check
    -- was actually about.
    if diag.stmtKey.isNone && diag.argKey.isNone then
      throwErrorAt (retRef.getD ref) head
    else
      throwErrorAt ref (head ++ m!"\n(no span for the failing statement — reported at the \
        program; this is a span-table gap, please report it)")

/-- **Is this term a program?** — asked of the VALUE, and answered by the calculus
    rather than by the surface.

    The first cut of this asked whether the block contained a `fn`, on the
    reasoning that a `fn` carries its own `-> retType` and so supplies the
    specification. That is true of the SPEC but false as a test of PROGRAM-hood,
    and the demo caught it immediately: `let x = Cons(1,Nil); let y = x; let z = x`
    is a use-after-move with no `fn` anywhere, and a syntactic test files it as a
    pure term and checks nothing.

    The right test already exists and is the calculus's own. `reflectC`'s refusal
    list — `.seal`, `.borrow`, `.assign`, `.seq`, `.matchE`, `.call`, an
    imperative λ — **IS this calculus's definition of the pure sub-grammar**
    (§1.3, quoted in `ProgMacro`'s header). So: a term ⇝ refuses is a program, and
    a term it accepts is pure. No second definition of the fragment boundary, and
    no way for the surface's opinion to drift from the kernel's.

    A `fn` still lands on the program side, because it emits a `let` of a `.seal`
    and `.seal` heads the refusal list.

    **It reads that list STRUCTURALLY (`Term.needsRuntime`) rather than by running
    `reflectC`, and the reason is correctness before cost.** Running the reflector
    in an empty Ω was the first implementation, and measured against the corpus it
    disagreed on 15 of 1096 blocks — every one of them a pure SPEC term that
    `readC` refuses only because nothing is bound to reflect it against:
    `Id (List Nat) (*%evT) (*%evT)` (a deref of a borrow parameter),
    `%(Std.lenFnT) %(Term.var vSlot)` (an application at a free runtime slot), the
    Σ-typed `…Honest`/`…Lie` specs of `ArraySort` and `S19Partition`. None is a
    program. Had the reflector stayed the classifier, all 15 would have been
    ⇒-walked and spuriously rejected — the "false program" direction, which breaks
    the build rather than merely missing a check.

    The lesson generalises: `readC`'s refusals are of two kinds, and only one of
    them is about the FRAGMENT. "This form has no comptime reading" is a statement
    about the grammar; "this variable is not bound here" is a statement about the
    state. Classification wants the first and must not read the second, so it asks
    the syntax, not the reflector. (It is also 2.6× faster — 6.5 s against 16.8 s
    over the corpus — but that is the lesser reason.) -/
def isProgramValue (v : Dllbc.Term) : Bool := Dllbc.Term.needsRuntime v

/-- Elaborate a block and check it with **the checker its content determines**.

    | content | ascription | check |
    |---|---|---|
    | classifies as a program | none | the ⇒-walk (`checkProgramDiag … none`) |
    | classifies as a program | `-> τ` | the walk AND the audit at `τ` |
    | pure | `-> τ` | `hasTypeT` against `τ` (`checkPureDiag`) |
    | pure | none | nothing — there is no specification anywhere |

    **"Classifies as a program" means `isProgramValue`, NOT "contains a `fn`".**
    The rows said `fn`-presence until this was corrected, and that is exactly the
    test the port refuted: `let x = Cons(1,Nil); let y = x; let z = x` is a
    use-after-move with no `fn` anywhere, and a syntactic reading files it as pure
    and checks nothing. A docstring naming a test the code does not perform is the
    one kind of comment this project treats as a defect, so it is named after the
    function above.

    The last row is information absence, not a deferral policy: a bare pure block
    states no type, and a λ is checkable but not synthesizable, so there is
    nothing any checker could be asked. The suite pairs a term with its type at
    the probe site precisely because the definition does not carry it.

    ## A block is checked when THREE things hold, and the table is only the first

    Stating all three together is what makes this a rule rather than a rule with
    exceptions bolted on:

    1. **It carries its own specification** — a program, or an ascription. The
       table above. Otherwise nothing can be asked.
    2. **Its value is closed** — no free variable, no unsolved metavariable. The
       spliced-template class: not comptime-known to the elaborator, so not
       askable. Tested on the `Expr`, body AND return type.
    3. **Its context is registry-resolvable** — every callee it names is bound
       inside the block. The FRAGMENT class: a closed block whose callee prefix
       arrives from a Lean-level assembler (`withPool (prog{ … })`, and the
       hashmap flagship's `hmS1Under`/`hmGmUnder`/`hmPinUnder`) is only half a
       program, and ⇒-walking it asks about a call table that has not been
       assembled yet.

    **(2) and (3) are the same idea at two levels**, which is why (3) completes
    this rule instead of puncturing it: context not registry-known is to (3) what
    value not comptime-known is to (2), and both say the elaborator has not been
    given enough to answer. Only (2) is detected here and declined silently; (3)
    is not detectable from the value alone — a fragment is indistinguishable from
    a program with a genuinely unknown callee — so it is the manual fence's
    population, 84 of the 297 sites. See docs/05 §2b and §6. -/
def elabChecked (ref : Syntax) (ret : Option (TSyntax `uterm))
    (act : UM (TSyntax `term)) : TermElabM Expr := do
  let (e, _) ← elabWith false act
  -- The RETURN TYPE is assembled before the closedness test, and is part of what
  -- that test is asked about. `prog check -> %ret { … }` — the twin-template
  -- shape, where the body is shared and only the type varies per instantiation —
  -- has a perfectly closed BODY and an open type, so testing the body alone
  -- would send an open `Expr` to `evalExpr` and take the kernel's
  -- "declaration has free variables" instead of deferring. Found the hard way.
  let retE ← ret.mapM fun r => do
    let (re, _) ← elabWith false (do let (t, _) ← elabUTerm [] [] 0 r; pure t)
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
  let isProgram := isProgramValue v
  let res :=
    if isProgram then checkProgramDiag v retVal
    else match retVal with
      -- A pure term with no stated type has no specification anywhere, so there
      -- is nothing to ask. Not a deferral: information absence. A λ is checkable
      -- but not synthesizable, which is why the suite pairs term and type at the
      -- probe site — the definition does not carry it.
      | none => .ok ()
      | some τ => checkPureDiag v τ
  let t2 ← IO.monoMsNow
  trace[Dllbc.check] "{if isProgram then "program" else "pure term"}: \
    reify {t1 - t0}ms, check {t2 - t1}ms"
  match res with
  | .ok _ => return e
  | .error diag =>
    -- THE SECOND WALK, and the only place one happens. The first ran without
    -- collecting spans, because a block that checks never reads them. This block
    -- did not check, so the table is now wanted: re-run the same walker action
    -- with collection on and map the breadcrumb through it. Re-walking a program
    -- that has already been rejected is free at human scale, and it is what buys
    -- "a block that passes pays nothing for its spans".
    let (_, spans) ← elabWith true act
    throwDiag ref (ret.map (·.raw)) spans diag

end ProgElab

open Surface ProgElab in
elab_rules : term
  | `(prog{ $b:ublk }) =>
    elabChecked b none (do let (t, _) ← elabUBlk [] [] 0 b; pure t)
  | `(prog -> $ret { $b:ublk }) =>
    elabChecked b (some ret) (do let (t, _) ← elabUBlk [] [] 0 b; pure t)
  -- THE FENCE, and it is the only annotation the information rule asks anyone to
  -- write. Its population is programs that exist BECAUSE they fail: a
  -- `progRejects` twin's rejection IS the assertion, so failing to elaborate
  -- would delete the test rather than strengthen it. Measured at 107 sites.
  | `(prog defer_check { $b:ublk }) =>
    elabUnchecked (do let (t, _) ← elabUBlk [] [] 0 b; pure t)

end Dllbc

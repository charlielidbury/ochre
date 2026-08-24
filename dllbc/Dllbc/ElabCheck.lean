import Dllbc.Program

open Lean

/-- **`x : τ` tooltips for DLLBC variables** (docs/16). On by default: the whole
    point is that hovering a variable in a `prog{ }` block answers, the way
    hovering a Lean variable does, without anyone opting in.

    It is an option rather than a constant because hover metadata is the one part
    of the diagnostic machinery collected on the SUCCESS path — a block that
    checks pays for it — so there has to be a way to turn it off and measure what
    it cost. Registered at the root rather than inside `Dllbc` so the name a user
    writes is the name it has. -/
register_option dllbc.hover : Bool := {
  defValue := true
  descr := "collect DLLBC hover types (`x : τ` tooltips) while elaborating `prog{ }` blocks"
}

/-- **Point hovers** (docs/17) — a tooltip answers about the reader's POSITION
    rather than about a binder: below a line that changed something, the variable
    shows what it changed to.

    **Default TRUE**, and the reason is the user's own statement of what a hover
    is for: "below the line where it got changed, the identifier shows the updated
    value". Binder granularity is a different answer to a different question, and
    it remains exactly one option-flip away — `set_option dllbc.pointHover false`
    restores docs/16's behaviour wholesale.

    The cost stopped being an argument either way once both ends were measured
    (docs/17 §9): recording is free, and reading is ~4 ms paid lazily inside
    `mkDocString?`, so nothing is computed for a tooltip nobody opens. -/
register_option dllbc.pointHover : Bool := {
  defValue := true
  descr := "answer hovers about the reader's position, not the binder (docs/17); false restores docs/16's binder granularity"
}

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
sites in this corpus are types and proof terms (`StdChain` alone is 135 of them),
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

`StdChain` imports this file, so the checking `prog{ }` reaches most of the
corpus transitively (its own 135 blocks are pure and check nothing).

**FORGETTING THE IMPORT IS A PARSE ERROR, NOT A SILENT SKIP — and the reason is
that the SYNTAX moved, not just the elaborator.** An earlier draft of this
paragraph claimed the opposite: that a module missing the import "would get the
LOW-level brace silently", the forgot-the-import-silently-unchecked failure mode,
and that routing through the pure library was what made forgetting it impossible. That
is wrong, and the build said so. `prog{` is declared HERE and nowhere else —
`ProgMacro` declares `ty{` — so a module that cannot see this file has no `prog{`
token at all and reports `unknown identifier 'prog'`. There is no low-level brace
left for it to fall back to.

This is the stronger guarantee and it is worth having deliberately: the failure
mode the transitive-import argument was constructed to avoid cannot occur,
because the two braces are different tokens rather than the same token with two
meanings. **The transitive-import argument was also empirically false**: four of
the 22 test modules (`Diff`, `Boundaries`, `Traces`, `Ledger`) never imported
the pure library at all. They now import this file directly, and each is self-
sufficient rather than inheriting from a neighbour — because inheriting is the
fragility, not the fix.

**INVARIANT, and it must survive any future move of this syntax.** Declaring
`prog` as a leading atom makes it a RESERVED TOKEN: `prog` can no longer be an
identifier anywhere downstream of this file. The corpus has no such identifier
today (checked), and the `->` forms below are written so the reservation is
not widened. If a future placement threatens this, stop and report rather than
widening it. -/

syntax "prog{" ublk "}" : term
-- `prog_parse { … }` is the PARSING STAGE alone: the block elaborates to a
-- `Term` and no judgment runs. A different operation from `prog{ }`, so a
-- different name rather than a flag on `prog` — its population is programs
-- that exist BECAUSE they fail (a `progRejects` twin's rejection is the
-- assertion) and library terms checked elsewhere.
syntax "prog_parse" "{" ublk "}" : term
-- **The module forms** (docs/20 stages 1-2): `prog () { … }` seeds the empty
-- state, `prog (e) { … }` seeds from the `Checked` that `e` evaluates to (both
-- of its twins — stage 6). Both elaborate
-- to a `Checked` — the term AND the walks' ending states — where the bare
-- `prog{ }` above keeps elaborating to a `Term`; hundreds of sites depend on
-- that, and the parenthesis is what says a state crosses the boundary. One
-- rule with an optional seed rather than two rules, because `()` is itself a
-- term and two rules would hand the parser an ambiguity.
syntax "prog" "(" (term)? ")" "{" ublk "}" : term

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

/-- Evaluate a seed expression to a `Checked` **value** (docs/20): the module
    elaborator needs the seed's actual checking state in hand — to resolve
    names against its Ω and to run the check from it — so the expression is
    evaluated the same way the assembled `Term` is. Cross-file the constant is
    compiled; same-file, the same machinery falls back to the interpreter. The
    whole `Checked` is evaluated (both twins), because the emitted value
    chains the seed's executing twin too; the elaborator itself reads only
    `.env`. -/
unsafe def evalCheckedUnsafe (e : Expr) : TermElabM Dllbc.Checked :=
  Meta.evalExpr' Dllbc.Checked ``Dllbc.Checked e

@[implemented_by evalCheckedUnsafe]
opaque evalCheckedValue (e : Expr) : TermElabM Dllbc.Checked

/-- `set_option trace.Dllbc.check true` reports, per program, the wall time spent
    reifying the value and the wall time spent checking — and says so when a
    program was declined rather than checked. -/
initialize registerTraceClass `Dllbc.check

/-- Run a walker action to an `Expr`, collecting spans only if asked.

    `collect := false` is the normal path and is what makes the passing case free
    (see `SpanAcc.collect`): the walker's span-filing calls become a boolean test
    and the emitted `Term` is byte-identical. The failing path re-runs the same
    action with `collect := true` to build the table it now needs. -/
def elabWith (collect : Bool) (hover : Bool) (act : UM (TSyntax `term)) :
    TermElabM (Expr × SpanAcc) := do
  let (stx, spans) ← liftMacroM (StateT.run act { collect, hover })
  let e ← elabTerm stx (some (mkConst ``Dllbc.Term))
  synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars e, spans)

/-! ## Hover tooltips (docs/16)

Two sources of truth meet here. The walker already resolved every identifier, so
what a PARAMETER's occurrence means is settled at elaboration time and arrives
rendered (`SpanAcc.hovers`). What a `let` binder means is settled only by the
⇒-walk, so those occurrences arrive as `(span, id, name)` and are joined against
the table `letStep` filed (`SpanAcc.occs` × `St.letTypes`).

Both end up as the same thing: an `Info.ofDelabTermInfo` leaf whose
`mkDocString?` overrides the hover text at that span. The override is total — no
Lean-level type line renders above it — which is what makes a DLLBC type the
whole answer rather than a footnote to a `Dllbc.Term`. -/

/-- Is this option on? -/
def hoverEnabled : TermElabM Bool := return dllbc.hover.get (← getOptions)

/-- Which σ ids does this rendered value mention?

    Asked of the RENDERED STRING rather than by walking the `Val`, and that is
    deliberate: the question is *which σs does the reader actually see?*, so it is
    asked of the very text the reader sees. A traversal would be answering a
    different question — which σs are present — and those differ wherever the
    renderer elides (a closure shows its λ and not its captured environment).

    It decides only WHICH substitutions to make; the substitution itself is the
    kernel's, so a mis-scan cannot mangle a value, only leave a σ bare. -/
def symsMentioned (s : String) : List Nat :=
  -- Split on the sigil and read the digits that open each piece: no recursion to
  -- justify, and in first-appearance order, which is the order the reader's eye
  -- meets them in the value. The digits are SUBSCRIPTS — `Dllbc.subNat` is how
  -- an index reaches rendered text, and this parser must stay its inverse.
  let isSub : Char → Bool := fun c => 0x2080 ≤ c.toNat && c.toNat ≤ 0x2089
  match s.splitOn "σ" with
  | [] => []
  | _ :: pieces =>
    pieces.foldl (fun acc p =>
      match p.toList.takeWhile isSub with
      | [] => acc
      | ds =>
        let n := ds.foldl (fun a d => a * 10 + (d.toNat - 0x2080)) 0
        if acc.contains n then acc else acc ++ [n]) []

/-- Give each σ in a value its type, inline, using the kernel's own refinement
    substitution — `substSym` with a `.const` carrying the annotated text, printed
    by the REAL `Val.pretty`. No parallel renderer and no new traversal.

    A σ with no `sctx` entry is left bare rather than annotated with a guess. -/
def annotateSyms (sctx : List (Nat × Dllbc.Term)) (v : Dllbc.Val) : Dllbc.Val :=
  (symsMentioned (Dllbc.Val.pretty v)).foldl (fun acc σ =>
    match sctx.lookup σ with
    | some τ => Dllbc.substSym σ (.const s!"(σ{Dllbc.subNat σ} : {Dllbc.Term.pretty τ})") acc
    | none => acc) v

/-- What the checker knew about a binder: `x ↦ v`, ONE form. Nothing a slot
    holds is timeless under strong updates, so there is no type-vs-value split
    and no caption classifying the answer — the contents are the answer, and a
    σ in them says exactly which parts are runtime-bound.

    The σs carry their types INLINE (`Cons (σ₀ : Nat) (σ₁ : List Nat)`), the
    user's own ruling over a trailing legend. No parallel renderer and no new
    traversal: each σ is replaced by `substSym` — the kernel's own refinement
    substitution, §3.2's — with a `.const` carrying the annotated text, and the
    REAL `Val.pretty` prints the result. `Term.prettyPrec` renders a `.const`
    as its bare name at every precedence, so the parens in the text are the
    ones that appear. -/
def letTooltip (name : String) (n : Dllbc.LetNote) : String :=
  s!"{name} ↦ {Dllbc.Val.pretty (annotateSyms n.sctx n.val)}"

/-- A binder's identity in the `let` table: its name and the key of the `let`
    statement that bound it (docs/22 §3 item 2) — so `let v` under a parameter
    `v`, or two `let v`s, are two entries and an occurrence joins to ITS binder
    or to none. -/
abbrev LetKey := String × Option Dllbc.Term

/-- First entry per binder, flagged when a later one disagrees.

    v1 is FIRST-PATH, per docs/16: a σ's type refines per branch, and a statement
    is checked once per path, so one binder legitimately has several binding-time
    types. Nothing is merged and no per-path list is shown; a disagreement is
    reported as one. The raw entries are compared rather than their renderings, so
    the flag costs no pretty-printing. An association list rather than a hash
    map, because the key carries a `Term`. -/
def letIndex (tbl : List Dllbc.LetNote) : List (LetKey × (Dllbc.LetNote × Bool)) :=
  tbl.foldl (fun m e =>
    let k : LetKey := (e.binder.name, e.stmtKey.map Dllbc.stmtKeyOf)
    match m.lookup k with
    | none => m ++ [(k, (e, false))]
    | some (e0, differs) =>
      -- Compared on what is DISPLAYED — the type and the value — and not on
      -- `sctx`, which rides along for the legend and whose growth between two
      -- paths is not a disagreement about this binder.
      if differs || (e0.ty? == e.ty? && e0.val == e.val) then m
      else m.map (fun kv => if kv.1 == k then (k, (e0, true)) else kv)) []

/-- Attach `text` as the hover content at `ref`. Positionless syntax is skipped:
    a leaf the server cannot locate is one nobody can hover. -/
def pushHover (ref : Syntax) (text : Unit → String) : TermElabM Unit := do
  if ref.getPos?.isNone then return
  pushInfoLeaf <| .ofDelabTermInfo {
    elaborator := .anonymous
    stx := ref
    lctx := (← getLCtx)
    expectedType? := none
    expr := mkConst ``Unit.unit
    isBinder := false
    -- **A THUNK, AND THAT IS THE WHOLE COST STORY FOR POINT HOVERS.**
    -- `mkDocString?` is documented as "computed only when it is used", so the
    -- text is built when someone hovers and never otherwise. That matters here in
    -- a way it did not for docs/16: a binder fact was a table lookup, but a POINT
    -- fact is a replay of the delta stream, measured at ~4 ms. Eagerly, a block
    -- with a hundred occurrences would pay four hundred milliseconds to compute
    -- tooltips nobody asked for; lazily it pays for the one that is read.
    mkDocString? := some fun _ => pure (text ())
  }

/-- Render what a binder held AT A POINT (docs/17), through `letTooltip` so a
    tooltip does not change shape when it changes granularity. -/
def pointTooltip (name : String) (v : Dllbc.Val) (sctx : List (Nat × Dllbc.Term)) : String :=
  letTooltip name { binder := Dllbc.Var.slot name, stmtKey := none, ty? := none, val := v, sctx := sctx }

/-- The point-fact for one occurrence, if its statement was walked and its binder
    was live there. `none` declines — see `replayTo`. An ENTRY occurrence (a
    telescope position) reads "entering the body" instead of "entering the
    statement" — `factsAtEntry`, the seeds' result. -/
def pointFactFor (pts : List (List Dllbc.PointDelta)) (o : Dllbc.Surface.OccNote)
    (keys : List Dllbc.Term) (i : Nat) :
    List (List (String × String) × Dllbc.Val × List (Nat × Dllbc.Term)) :=
  match keys[i]? with
  | none => []
  | some key =>
    if o.entry then Dllbc.factsAtEntry pts key o.name
    else Dllbc.factsAt pts key o.name

/-- `x ⇒ Cons, n ⇒ S` — which arms this path took, outermost first. -/
def trailText (trail : List (String × String)) : String :=
  ", ".intercalate (trail.reverse.map fun p => s!"{p.1} ⇒ {p.2}")

/-- How many differing per-path answers a tooltip shows before it stops listing.

    **A cap, not a summary.** Three is enough to see that the paths disagree and
    how; past that the tooltip stops being a tooltip. What is over the cap is
    COUNTED rather than dropped silently, because "and 4 more" is information and
    an unannounced truncation is a lie. -/
def pathCap : Nat := 3

/-- Render the per-path answers for one occurrence.

    When every path agrees there is one answer and no ceremony — which is the
    common case, and it must not be made to look conditional. When they disagree
    each answer is labelled with the arm trail that produced it, because "which
    path" is the other half of the answer (docs/05's own argument for putting the
    trail in error messages, applied to tooltips). -/
def renderPaths (solo body : Dllbc.Val → List (Nat × Dllbc.Term) → String)
    (facts : List (List (String × String) × Dllbc.Val × List (Nat × Dllbc.Term))) :
    Option String :=
  match facts with
  | [] => none
  | _ =>
    -- Distinctness is decided on the SHORT body so two paths that differ only in
    -- how the solo form would caption them do not read as a disagreement.
    let rendered := facts.map fun (tr, v, sctx) => (tr, body v sctx, v, sctx)
    let distinct := rendered.foldl (fun acc p =>
      if acc.any (fun q => q.2.1 == p.2.1) then acc else acc ++ [p]) []
    match distinct with
    -- Every path agrees: one answer, rendered in full, with no ceremony implying
    -- it was conditional.
    | [(_, _, v, sctx)] => some (solo v sctx)
    | [] => none
    | _ =>
      let shown := distinct.take pathCap
      let extra := distinct.length - shown.length
      let listed := "; ".intercalate (shown.map fun (tr, txt, _, _) =>
        if tr.isEmpty then txt else s!"{txt} *(on {trailText tr})*")
      some (listed ++ if extra > 0 then s!"; *…and {extra} more path(s)*" else "")

/-- One path's answer WITHOUT the name — for per-path listings, where the name
    repeating once per path would be noise. Also the string per-path
    DISTINCTNESS is decided on (see `renderPaths`). -/
def pointBody (v : Dllbc.Val) (sctx : List (Nat × Dllbc.Term)) : String :=
  Dllbc.Val.pretty (annotateSyms sctx v)

/-- Reify accumulated key syntaxes into key **values**, to match a breadcrumb. -/
def keyValues (keys : Array Syntax) : TermElabM (List Dllbc.Term) := do
  let elems : Array (TSyntax `term) := keys.map fun k => ⟨k⟩
  let e ← elabTerm (← `(([$elems,*] : List Dllbc.Term)))
    (some (mkApp (mkConst ``List [levelZero]) (mkConst ``Dllbc.Term)))
  synthesizeSyntheticMVarsNoPostponing
  evalKeysValue (← instantiateMVars e)

/-- Push every tooltip this block earned: the walker's own, then the checker's
    joined onto the occurrences that need them. An occurrence with no entry is
    passed over in silence — unlike a missing SPAN, which is a defect worth
    reporting, a missing type is the ordinary case for a block that was never
    checked (`prog_parse`, or a splice) and for a binder no path reached. -/
def pushHovers (spans : SpanAcc) (tbl : List Dllbc.LetNote)
    (pts : List (List Dllbc.PointDelta)) : TermElabM Unit := do
  for (ref, text) in spans.hovers do
    pushHover ref (fun _ => text)
  unless spans.occs.isEmpty do
    let idx := letIndex tbl
    -- POINT FACTS FIRST, binder facts as the fallback. The point answer is
    -- strictly more specific — it is about where the reader is — so it wins
    -- wherever it exists, and where it does not (no deltas, an untagged
    -- occurrence, a binder not live at that point) the binder answer still
    -- serves. Neither guesses: both decline rather than approximating.
    -- Surface keys are built from EMITTED syntax, markers included; the delta
    -- stream's keys come from the stripped walk (docs/21 §5). Strip here or a
    -- point answer inside a marked statement silently declines.
    let keys ← if pts.isEmpty then pure [] else
      (·.map Dllbc.Term.stripMarkers) <$> keyValues (spans.occs.filterMap (fun o => o.stmt))
    -- The binder keys, evaluated the same way, for the `let`-table join —
    -- stripped for the same reason: `LetNote.stmtKey` comes from the stripped
    -- walk, and the emitted `let` key may carry a marker in its right-hand side.
    let bkeys ← if tbl.isEmpty then pure [] else
      (·.map Dllbc.Term.stripMarkers) <$> keyValues (spans.occs.filterMap (fun o => o.bindKey))
    let mut ki := 0
    let mut bi := 0
    for oi in [0 : spans.occs.size] do
      let o := spans.occs[oi]!
      -- Nothing is computed here — `hasPoint` only asks whether this occurrence
      -- HAS a point answer, and the answer itself is built inside the thunk.
      let hasPoint := o.stmt.isSome && !pts.isEmpty && !(pointFactFor pts o keys ki).isEmpty
      let ki' := ki
      let point? : Option (Unit → String) :=
        if hasPoint then
          some (fun _ => (renderPaths (pointTooltip o.name)
                          pointBody (pointFactFor pts o keys ki')).getD "")
        else none
      if o.stmt.isSome && !pts.isEmpty then ki := ki + 1
      -- The binder fact this occurrence may fall back to: the entry under its
      -- name AND the key of the `let` it resolved to. No `let` (a parameter, a
      -- pattern binder) — no fallback.
      let binderFact : Option (Dllbc.LetNote × Bool) :=
        if o.bindKey.isSome && !tbl.isEmpty then
          match bkeys[bi]? with
          | some bk => idx.lookup (o.name, some (Dllbc.stmtKeyOf bk))
          | none => none
        else none
      if o.bindKey.isSome && !tbl.isEmpty then bi := bi + 1
      -- **`show x` — the SAME answer, eagerly, as a diagnostic** (docs/18). Not a
      -- second renderer and not a second query: the string below is the one the
      -- tooltip would have produced at this occurrence, forced now instead of
      -- when someone points at it. If these could disagree a reader would have to
      -- know which to believe, so they are one call.
      if spans.showOccs.contains oi then
        let shown := match point? with
          | some txt => txt ()
          | none =>
            match binderFact with
            | some (e, differs) =>
              letTooltip o.name e ++ (if differs then " *(differs per path)*" else "")
            -- Nothing known: say so rather than printing an empty box. A `show`
            -- is an author's explicit request, so silence would read as a bug.
            | none => s!"{o.name} — no value here (not checked, or not live)"
        logInfoAt o.ref shown
      -- The static annotation channel is GONE (user ruling, 2026-08-21): under
      -- strong updates nothing about a slot is timeless, so the annotation's
      -- scope-wide "x : τ" claim is one the calculus does not make. The point
      -- answer is the whole answer — telescope positions included, via ENTRY
      -- occurrences — the binder fact recorded AT THE BINDING is the fallback,
      -- and with neither the tooltip declines rather than echoing the source.
      match point? with
      | some txt => pushHover o.ref txt
      | none =>
        if let some (e, differs) := binderFact then
          pushHover o.ref (fun _ => letTooltip o.name e ++
            if differs then " *(differs per path)*" else "")

/-- Elaborate a block and check NOTHING — the fence. Same value as `prog{ }`
    produces, without the check that would reject it.

    S1 hovers still fire here, and that is the design rather than a leak: a
    parameter's type is its ANNOTATION, which is written in the source whether
    anything checked it or not. S2 hovers do not, and cannot — no walk ran, so no
    Ω existed to read a `let`'s type out of. -/
def elabUnchecked (act : UM (TSyntax `term)) : TermElabM Expr := do
  let hover ← hoverEnabled
  let (e, spans) ← elabWith false hover act
  if hover then pushHovers spans [] []
  return e


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
  -- Both norms strip markers FIRST (docs/21 §5): the crumb is from the stripped
  -- walk, the keys are from emitted syntax — and stripping before `stmtKeyOf`
  -- rather than after, because a marker wrapping a whole statement would push
  -- `stmtKeyOf` into its catch-all and keep the continuation the machine's key
  -- dropped.
  let hit ← do
    match ← find Dllbc.Term.stripMarkers spans.args diag.argKey with
    | some h => pure (some h)
    | none => find (fun k => Dllbc.stmtKeyOf (Dllbc.Term.stripMarkers k)) spans.stmts diag.stmtKey
  match hit with
  | some (r, dup) =>
    let note := if dup then m!"\n(this statement is written more than once in the program; \
      the position shown is its first occurrence)" else m!""
    throwErrorAt r (head ++ note)
  | none =>
    -- NO BREADCRUMB AT ALL versus A BREADCRUMB THAT DID NOT MATCH. Only the
    -- second is a defect. Some rejections legitimately carry no breadcrumb — a
    -- verdict reached without locating a statement, which has no span to find —
    -- and telling the author to report a span-table gap for one of those would
    -- send them after a bug that is not there. That case reports at the block.
    --
    -- The one class that HAS reached the gap branch was a key that was stale
    -- rather than missing: a statement keyed by its own term, filed before
    -- `bindFn` retargeted the sibling-`fn` calls inside it (`Uni.rekeySpansFrom`).
    if diag.stmtKey.isNone && diag.argKey.isNone then
      throwErrorAt (retRef.getD ref) head
    else
      throwErrorAt ref (head ++ m!"\n(no span for the failing statement — reported at the \
        program; this is a span-table gap, please report it)")

/-- Elaborate a block and CHECK IT. There is no routing and no second checker.

    Every block gets the top-level ⇒-walk (`checkProgramDiag … none`). The
    intra-term staging is not this function's business: it is the author's own
    per-binder capitalization, which `letStep` reads on the way through (⇝ for a
    capital binder, ⇒ for a lowercase one — `Machine.lean`, shared by `readR`,
    `readRTail` and `exploreD`, so the checking driver inherits it).

    A block that wants to state an intended type says so with a **seal**,
    `(e : τ)`, and the seal's own symbolic-⇒ rule verifies it at the node. That is
    why there is no `-> τ` parameter here and no pure-checking path: the calculus
    already had the type-carrier, and its rule *is* the audit (`Syntax.lean`, the
    `.seal` constructor).

    The one thing that is NOT checked is a block whose assembled value is not
    closed — a spliced template. It has nothing to evaluate, and it is checked at
    its instantiations by construction. That is detected here and declined
    silently with a trace line.

    Everything else that should not be checked says so in the source, with
    `prog_parse { … }`: a block constructed for later checking at its probe.

    **Historical note, because the docstring here has been wrong twice and both
    errors were the same kind.** It first described the classifier as testing for
    `fn`-presence, which the code never did (it called `Term.needsRuntime`); the
    correction was made, and then the classifier itself was deleted, leaving the
    corrected table describing a routing that no longer exists. A comment naming a
    test the code does not perform is the one kind this project treats as a
    defect, and proximity is no protection — both versions sat two lines above the
    function they misdescribed. -/
def elabChecked (ref : Syntax) (act : UM (TSyntax `term)) : TermElabM Expr := do
  let hover ← hoverEnabled
  let (e, spans) ← elabWith false hover act
  let isOpen (x : Expr) : Bool := x.hasMVar || x.hasFVar
  if isOpen e then
    trace[Dllbc.check] "DEFERRED — the assembled value is not closed (a splice of \
      a local, or an unsolved metavariable). It is checked where it is \
      instantiated."
    -- S1 only, for the reason `elabUnchecked` gives: the annotations are in the
    -- source, and nothing walked.
    if hover then pushHovers spans [] []
    return e
  let t0 ← IO.monoMsNow
  let v ← evalTermValue e
  let t1 ← IO.monoMsNow
  -- ONE CHECKER, NO ROUTING. The classifier is gone: every block gets the
  -- top-level ⇒-walk, and the intra-term staging is done by the author's own
  -- per-binder capitalization, which `letStep` already reads (⇝ for a capital
  -- binder, ⇒ for a lowercase one — Machine.lean, shared by all three drivers).
  -- A term that wants a stated type says so with a SEAL, `(e : τ)`, whose
  -- symbolic-⇒ rule verifies it at the node; there is no `-> τ` side-channel and
  -- no separate pure path.
  -- Same walk either way (`checkProgramHover` is `checkProgramDiag`'s paths and
  -- verdict with the seed's `hover` flag flipped), so the accept/reject decision
  -- does not depend on whether anyone is collecting tooltips.
  let pointHover ← (return dllbc.pointHover.get (← getOptions))
  let res :=
    if hover then checkProgramHover v none pointHover
    else (checkProgramDiag v none).map (fun _ => ([], []))
  let t2 ← IO.monoMsNow
  trace[Dllbc.check] "checked: reify {t1 - t0}ms, check {t2 - t1}ms"
  match res with
  | .ok (tbl, pts) =>
    -- THE HOVER PUSH IS ON THE SUCCESS PATH, and that is the one structural way
    -- this feature differs from the error spans beside it (docs/16): a squiggle
    -- costs nothing until something fails, a tooltip costs on every block that
    -- checks. Which is why the option above exists and why the cost is measured.
    if hover then pushHovers spans tbl pts
    -- docs/17 §9's instrument: the delta count is how a measurement run confirms
    -- the option reached the checker instead of measuring nothing.
    unless pts.isEmpty do trace[Dllbc.check] "point deltas: {pts.length}"
    return e
  | .error diag =>
    -- THE SECOND WALK, and the only place one happens. The first ran without
    -- collecting spans, because a block that checks never reads them. This block
    -- did not check, so the table is now wanted: re-run the same walker action
    -- with collection on and map the breadcrumb through it. Re-walking a program
    -- that has already been rejected is free at human scale, and it is what buys
    -- "a block that passes pays nothing for its spans".
    let (_, spans) ← elabWith true false act
    throwDiag ref none spans diag

/-- **Elaborate a module block** (docs/20 stages 1-2): the `prog () { … }` /
    `prog (e) { … }` forms, producing a `Checked`.

    The seed expression is evaluated to a `Checked` FIRST, because two things
    need its checking state before the block's own syntax can be walked: name resolution
    (stage 2 — the seed's Ω entries go into the surface's scope, so an
    identifier or call that resolves to nothing local resolves against the seed
    by name) and the check itself, which runs seeded — the same walk
    `moduleFinalSt` performs, with the hover ledgers collected on top.

    What differs from `elabChecked`, and why each difference is the design:
      * the walk starts at the seed, not `initSt` — seeding IS a parameter
        substitution (stage 0);
      * no `endScope` — a module's bindings persist by definition;
      * single path REQUIRED — a forking block has no one ending state;
      * an open value (a splice of a local) is an ERROR, not a deferral: a
        `Checked` cannot exist without its ending state, and there is no term
        to walk;
      * mode is pinned to checking (`modulePathsD`).

    The emitted value is `Checked.seeded <seed> <raw term> <hints> <spans>` —
    the state is re-derived on demand by the same pure walk, so no `ToExpr St`
    exists anywhere; the two trailing arguments (stage 3) are the plain-data
    module-boundary channels only this elaboration can supply, quoted rather
    than derived. -/
def elabModule (ref : Syntax) (seed? : Option (TSyntax `term)) (b : TSyntax `ublk) :
    TermElabM Expr := do
  let seedE ← match seed? with
    | some s => do
      let e ← elabTerm s (some (mkConst ``Dllbc.Checked))
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    | none => pure (mkConst ``Dllbc.Checked.init)
  if seedE.hasMVar || seedE.hasFVar then
    throwErrorAt ((seed?.map (·.raw)).getD ref) "prog (…): the seed must be a \
      closed `Checked` expression — it is evaluated during elaboration, so a \
      local or an unsolved metavariable has no value to evaluate to"
  -- The CHECKING twin is the elaborator's state: scope and the diagnostic
  -- walk both read it. The executing twin is chained at the value level by
  -- `Checked.seeded`; nothing here runs anything.
  let seedSt := (← evalCheckedValue seedE).env
  -- Stage 2, the scope half: every seed Ω entry is in surface scope by name.
  -- Newest FIRST (the reverse of Ω's append order), so a later binding of a
  -- name shadows an earlier one exactly as Ω's own newest-wins resolution
  -- (`findSlot?`) reads it, and the block's own binders — consed on in front —
  -- shadow imports. A declaration entry (`decl`) resolves as a fn slot: a bare
  -- mention becomes `.var name`, and a CALL falls through to `.call` for
  -- `moduleRetarget` to rewrite — the same division of labour local `fn`s get.
  let seedScope : Scope :=
    (seedSt.env.map (fun kv => (⟨kv.1.name, kv.1.kind, none⟩ : Scoped))).reverse
  let act : UM (TSyntax `term) := elabUBlk seedScope b
  let hover ← hoverEnabled
  -- `collect := true`, unlike `elabChecked` — the one deliberate cost reversal
  -- (docs/20 stage 3). For a plain block the span table exists to locate a
  -- rejection, so the passing path skips it; for a MODULE the table is carried
  -- data — it persists in the block's ending state (`Ledgers.spans`) so later
  -- blocks know where their imports were written — and a table that is wanted
  -- on the passing path has to be collected on it. Module blocks are few; the
  -- +6.9% that made `collect` opt-in was measured over every `ty{ }` in the
  -- corpus.
  let (e, spans) ← elabWith true hover act
  if e.hasMVar || e.hasFVar then
    throwErrorAt ref "prog (…): a module block must assemble to a closed value \
      — its check and its ending state are computed at elaboration, so a splice \
      of a local (deferred in a plain prog block) cannot appear here"
  let t0 ← IO.monoMsNow
  let v ← evalTermValue e
  let vr := Dllbc.moduleRetarget seedSt v
  let t1 ← IO.monoMsNow
  let pointHover ← (return dllbc.pointHover.get (← getOptions))
  -- The SAME walk `Checked.seeded` will run at the value level, with the hover
  -- ledgers collected on top; `moduleFinalSt` pins those off, so the persisted
  -- state and this one differ in ledgers only — the plan's judgment-equivalence.
  let (_, paths) := Dllbc.modulePathsD { seedSt with hover, pointHover } vr
  let t2 ← IO.monoMsNow
  trace[Dllbc.check] "module: reify {t1 - t0}ms, check {t2 - t1}ms"
  match paths with
  | [.ok (_, st)] =>
    if hover then
      pushHovers spans st.ledgers.letTypes.reverse
        (st.ledgers.points.reverse :: st.ledgers.paths)
    -- Stage 3: the module-boundary channels, quoted as plain data into the
    -- emitted value. These are the two facts about the block the value-level
    -- walk cannot re-derive — the `[k]` hint died at the macro layer, the
    -- spans at the syntax layer — so they ride the `Checked.seeded` call as
    -- arguments rather than being recomputed.
    --
    -- Hints: newest first (matching Ω's newest-wins resolution), restricted to
    -- names that survived to the module's ending Ω — a `fn` declared inside
    -- another `fn`'s body filed an entry too, but its binding died with the
    -- sealed body and no consumer can call it. (Residual ambiguity: a
    -- body-local fn SHARING a top-level fn's name keeps its entry; the newest
    -- filing wins the lookup, which is the top-level one whenever the
    -- top-level declaration comes later in the block.)
    let hintList : List (String × Nat) :=
      spans.fnHints.toList.reverse.filter fun p =>
        st.env.any (fun kv => kv.1.isDecl && kv.1.name == p.1)
    -- Spans: each statement key elaborates to its term — the same round-trip
    -- `keyValues` does on the failing path — normalized HERE via `stmtKeyOf`
    -- (Uni cannot name it; this module can, see `spanFor`), so the persisted
    -- channel is directly joinable against a breadcrumb. A key with no
    -- position (synthesized syntax) is skipped, not guessed at. Markers are
    -- stripped FIRST (docs/21 §5, the third key join): the emitted key carries
    -- them, the breadcrumb a later seeded walk files never does.
    let modName := toString (← getMainModule)
    let noteStxs : Array (TSyntax `term) ← spans.stmts.filterMapM fun (k, r) => do
      match r.getPos?, r.getTailPos? with
      | some lo, some hi =>
        return some (← `(Dllbc.SpanNote.mk (Dllbc.stmtKeyOf (Dllbc.Term.stripMarkers $(⟨k⟩)))
            $(quote modName) $(quote lo.byteIdx) $(quote hi.byteIdx)))
      | _, _ => return none
    let spansE ← elabTerm (← `(([$noteStxs,*] : List Dllbc.SpanNote)))
      (some (mkApp (mkConst ``List [levelZero]) (mkConst ``Dllbc.SpanNote)))
    synthesizeSyntheticMVarsNoPostponing
    let spansE ← instantiateMVars spansE
    return mkApp4 (mkConst ``Dllbc.Checked.seeded) seedE e (toExpr hintList) spansE
  | _ =>
    match paths.findSome? (fun r => match r with | .error d => some d | .ok _ => none) with
    | some diag =>
      let (_, spans) ← elabWith true false act
      throwDiag ref none spans diag
    | none =>
      throwErrorAt ref m!"prog (…): the module walk forked into {paths.length} \
        paths; a module must be single-path, so its one ending state is \
        well-defined"

end ProgElab

open Surface ProgElab in
elab_rules : term
  | `(prog{ $b:ublk }) =>
    elabChecked b (elabUBlk [] b)
  | `(prog_parse { $b:ublk }) =>
    elabUnchecked (do
      modify fun a => { a with parse := true }
      elabUBlk [] b)
  -- The module forms (docs/20). One elaborator, seed optional: `()` is the
  -- empty state, `(e)` is a state to continue from.
  | `(prog ($[$e:term]?) { $b:ublk }) => elabModule b e b

end Dllbc

import Lean
import Dllbc.Compile

/-!
# `Dllbc.CompileCmd` — the command that makes a DLLBC program into Lean `def`s

`Dllbc.Compile` gets as far as Lean *source text*. This is the last step: parse
that text with Lean's own parser and elaborate it, so the `def`s land in the
environment and can be applied, `#eval`'d, and proved about like anything else.

    compile_dllbc P1 from p1

emits `P1.Double : Nat → Nat`, `P1.r : Nat`, `P1.main : Nat`, where `p1` is any
Lean expression of type `Dllbc.Term` — typically a `prog{ … }`.

**Why source text and not hand-built `Expr`s.** A probe's job is to be readable
and to fail loudly. Going through the parser means the generated program can be
printed (`#dllbc_source`), pasted into a file, and diffed; and a rendering bug is
a parse error naming a column rather than an `Expr` that elaborates to something
subtly wrong. The cost is that the compiler cannot exploit anything the parser
cannot express, which for this fragment is nothing.
-/

open Lean Elab Command

namespace Dllbc.Compile

/-- Elaborate one generated command, or report where the parser stopped. -/
def elabGenerated (src : String) : CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command src with
  | .ok stx => elabCommand stx
  | .error err => throwError "generated code failed to parse:\n{src}\n---\n{err}"

/-! ## Getting the `Term` out of the syntax

    `Term.evalTerm` runs the compiled definition the syntax denotes, which is how
    the command gets from `prog{ … }` (a Lean expression) to a `Dllbc.Term` (a
    value it can walk). It is `unsafe` — it interprets compiled code — so the two
    commands are written as one `unsafe` worker behind an `implemented_by`
    façade, the standard way to reach `evalExpr` from an `elab`. -/

/-- Emit (or print) the compiled program. `printOnly` splits the two commands,
    which are otherwise identical. -/
unsafe def compileWorkerUnsafe (printOnly : Bool) (ns : String) (t : Syntax) :
    CommandElabM Unit := do
  let prog ← liftTermElabM (Term.evalTerm Dllbc.Term (mkConst ``Dllbc.Term) t)
  match compileProgram prog with
  | .error e =>
    if printOnly then logInfo s!"DLLBC compilation FAILED: {e}"
    else throwError "DLLBC compilation failed: {e}"
  | .ok cp =>
    if printOnly then
      match cp.renderSource ns with
      | .error e => logInfo s!"rendering FAILED: {e}"
      | .ok s => logInfo s
    else
      match cp.renderCommands ns with
      | .error e => throwError "rendering failed: {e}"
      | .ok cmds => for c in cmds do elabGenerated c

@[implemented_by compileWorkerUnsafe]
opaque compileWorker (printOnly : Bool) (ns : String) (t : Syntax) : CommandElabM Unit

/-- `compile_dllbc NS from e` — compile the DLLBC program `e` into Lean `def`s
    under namespace `NS`. -/
elab "compile_dllbc " ns:ident " from " t:term : command =>
  compileWorker false ns.getId.toString t

/-- `#dllbc_source NS from e` — print what `compile_dllbc` would emit, without
    emitting it. The probe's window on the compiler. -/
elab "#dllbc_source " ns:ident " from " t:term : command =>
  compileWorker true ns.getId.toString t

/-! ## The bulk form — a LIST of programs, one `def` each

    The differential's generated corpus is 45 programs, and a differential that
    covers three of them by hand is not a measurement. This compiles a whole
    `List Term` — one monolithic `def` per program, plus an `all` collecting them
    — so the assertion can be a single `native_decide` over the zip of the source
    programs with their compiled values. -/

unsafe def compileEachUnsafe (ns : String) (t : Syntax) : CommandElabM Unit := do
  let progs ← liftTermElabM
    (Term.evalTerm (List Dllbc.Term) (mkApp (mkConst ``List [levelZero]) (mkConst ``Dllbc.Term)) t)
  let mut srcs : List String := []
  let mut names : List String := []
  let mut ty : String := "Unit"
  for (p, i) in progs.zip (List.range progs.length) do
    match compileProgram p with
    | .error e => throwError "program #{i} failed to compile: {e}"
    | .ok cp =>
      match cp.mono.render with
      | .error e => throwError "program #{i} failed to render: {e}"
      | .ok body =>
        ty := cp.mainTy.render
        names := names ++ [s!"f{i}"]
        srcs := srcs ++ [s!"def f{i} : {ty} :=\n  {body}"]
  let allDef := s!"def all : (List {ty}) := [{String.intercalate ", " names}]"
  for c in ["namespace " ++ ns] ++ srcs ++ [allDef, "end " ++ ns] do
    elabGenerated c

@[implemented_by compileEachUnsafe]
opaque compileEach (ns : String) (t : Syntax) : CommandElabM Unit

/-- `compile_dllbc_each NS from es` — compile every program in the `List Term`
    `es`, as `NS.f0 … NS.fn`, and collect them in `NS.all`. -/
elab "compile_dllbc_each " ns:ident " from " t:term : command =>
  compileEach ns.getId.toString t

end Dllbc.Compile

import Lean
import Ochr

/-! # The verdict driver

`lake -q exe check` runs the Ochr checker on the blocks of `HashMap.lean` and prints each
block's verdict table: every declaration, whether it is expected to be accepted (`def`) or
rejected (`reject def`), and the checker's verdict, with the reason for a rejection.

    lake -q exe check                    every block
    lake -q exe check HashMapSolution    only the named blocks (quicker while you work on proofs)
    lake -q exe check --trace NAME       the checker's trace for declaration NAME: the goal, the
                                      case splits, the types of calls
    lake -q exe check --machine          one tab-separated line per declaration (for grade.sh)
    lake -q exe check --outline FILE     what FILE is made of, by Lean's parser (for grade.sh)

The driver reads `HashMap.lean` itself, with Lean's front end, rather than importing it, so
it works while declarations are still rejected. -/

open Lean Ochr.Test

def solutionFile : String := "HashMap.lean"

def blockNames : List Name :=
  [`HashMapSpec, `HashMapSolution, `HashMapTests]

-- The machine's step budget per declaration: ample for every test.
def fuel : Nat := 50000000

/-- The module names an import command mentions. -/
partial def idents (s : Syntax) : Array Name :=
  if s.isIdent then #[s.getId] else s.getArgs.foldl (fun acc a => acc ++ idents a) #[]

/-- `--outline FILE`: the imports, then each top-level command's kind (and an `ochr` block's
name), then every parse error. -/
unsafe def outline (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, st, msgs) ← Parser.parseHeader inputCtx
  for n in idents header.raw do
    IO.println s!"IMPORT\t{n}"
  let env ← importModules #[{ module := `Ochr }] {} (loadExts := true)
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let mut st := st
  let mut msgs := msgs
  repeat
    let (cmd, st', msgs') := Parser.parseCommand inputCtx pmctx st msgs
    st := st'
    msgs := msgs'
    if Parser.isTerminalCommand cmd then break
    let line := (inputCtx.fileMap.toPosition (cmd.getPos?.getD 0)).line
    let name := if cmd.getKind == `Ochr.Notation.ochrProgram then cmd[1].getId.toString else ""
    IO.println s!"CMD\t{cmd.getKind}\t{name}\t{line}"
  for m in msgs.toList do
    IO.println s!"ERROR\t{(← m.toString).replace "\n" " "}"
  return 0

/-- The blocks of the solution file, elaborated by Lean's front end (every error it reports
is printed to stderr), in the order of `blockNames`; a block that is missing is left out. -/
unsafe def loadBlocks : IO (List (String × Ochr.Surface.Block)) := do
  let input ← IO.FS.readFile solutionFile
  let inputCtx := Parser.mkInputContext input solutionFile
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx
  let s ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages {})
  let env := s.commandState.env
  let mut out := []
  for n in blockNames do
    match env.evalConst Ochr.Surface.Block {} n with
    | .ok b => out := out ++ [(n.toString, b)]
    | .error _ => IO.eprintln s!"block {n} is missing from {solutionFile}"
  return out

unsafe def mainImpl (args : List String) : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  if let ["--outline", path] := args then return ← outline path
  let blocks ← loadBlocks
  match args with
  | ["--machine"] =>
    for (n, b) in blocks do
      for r in (Ochr.Test.run n b {} fuel).rows do
        -- the reason, as `Row.show` prints it (whatever fields the checker's `Verdict` has)
        let msg := match r.show.splitOn ") rejected: " with
          | _ :: rest@(_ :: _) => ") rejected: ".intercalate rest
          | _ => ""
        let got := if r.verdict.ok then "accepted" else "rejected"
        let msg := (msg.replace "\n" " ").replace "\t" " "
        IO.println s!"ROW\t{n}\t{r.name}\t{if r.expectAccept then "accept" else "reject"}\t{got}\t{msg}"
    return 0
  | ["--trace", name] =>
    for (n, b) in blocks do
      let rep := Ochr.Test.run n b { trace := true } fuel
      if rep.rows.any (·.name == name) then
        IO.println (rep.showTrace name)
        return 0
    IO.eprintln s!"no declaration {name} in {", ".intercalate (blocks.map (·.1))}"
    return 1
  | names =>
    let chosen := if names.isEmpty then blocks else blocks.filter (names.contains ·.1)
    if chosen.length != names.length && !names.isEmpty then
      IO.eprintln s!"unknown block; the blocks are {", ".intercalate (blocks.map (·.1))}"
      return 2
    for (n, b) in chosen do
      IO.println (Ochr.Test.run n b {} fuel).show
    return 0

@[implemented_by mainImpl]
opaque runSafe (args : List String) : IO UInt32

def main (args : List String) : IO UInt32 := runSafe args

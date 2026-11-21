import Lean
import Ochr.Run
open Lean Elab Command

/-! # What the checker runs that the kernel cannot see into (D109)

Dev tooling, not checker code. Walks every constant reachable from `Ochr.Test.checkProgram`
through types and kernel-visible values, and prints those the kernel cannot see into: opaque
constants (a `partial def` compiles to one, and so does Lean's `while` and `repeat`, through
`Loop.forIn` and `repeatM`), partial or unsafe ones, and checker (`Ochr`) constants with an
`implemented_by`. Each is printed with the chain of constants that reaches it, up to the nearest
checker constant. Run after a green `lake build`:
`lake env lean Scratch/Reach.lean`. On D109 (2026-11-21) the one checker constant listed is
`Ochr.termAddr`, the standard's sanctioned exception; the rest are Lean's own library (string
primitives, formatting, a platform constant, an iterator fix), reached through messages, printing,
the editor's location table and a block's printed parameter names. Before D109,
`_private.Init.While.0.repeatM.impl` was listed too, reached from `blockCaptures`' `while`. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`Ochr.Test.checkProgram]
  let mut bad : Array String := #[]
  let mut count := 0
  let mut parent : NameMap Name := {}
  for _ in [0:10000000] do
    if todo.isEmpty then break
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    count := count + 1
    let some ci := env.find? n | continue
    let kind := match ci with
      | .opaqueInfo _ => some "opaque"
      | _ => none
    let impl := Lean.Compiler.getImplementedBy? env n
    -- what the kernel cannot see into: an opaque constant (a `partial def`, a `while` through
    -- `Loop.forIn`, an `opaque`), or a partial or unsafe one; `implemented_by` with a kernel-visible
    -- definition only changes the compiled code, and is listed separately
    let flags := (if let some k := kind then [k] else []) ++
      (if ci.isUnsafe then ["unsafe"] else []) ++
      (if ci.isPartial then ["partial"] else []) ++
      (if kind.isNone && impl.isSome && n.getRoot == `Ochr then [s!"implemented_by {impl.get!}"] else [])
    unless flags.isEmpty do
      -- the chain of constants that reaches it, up to the nearest checker (`Ochr`) constant
      let mut chain : List Name := []
      let mut cur := n
      for _ in [0:100] do
        let some p := parent.find? cur | break
        chain := chain ++ [p]
        if p.getRoot == `Ochr then break
        cur := p
      bad := bad.push s!"{n}: {", ".intercalate flags}  <- {" <- ".intercalate (chain.map toString)}"
    let used := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[])
    for u in used do
      unless seen.contains u do
        unless parent.contains u do parent := parent.insert u n
        todo := todo.push u
  IO.println s!"reachable constants: {count}"
  for b in bad.qsort (· < ·) do IO.println b

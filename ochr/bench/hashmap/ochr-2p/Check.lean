import HashMap
open Ochr.Test

/-! # The verdict driver

`lake exe check` runs the Ochr checker on the blocks of `HashMap.lean` and prints each
block's verdict table: every declaration, whether it is expected to be accepted (`def`) or
rejected (`reject def`), and the checker's verdict, with the reason for a rejection.

    lake exe check                    every block
    lake exe check HashMapModel       only the named blocks (quicker while you work on proofs)
    lake exe check --trace NAME       the checker's trace for declaration NAME: the goal, the
                                      case splits, the types of calls
    lake exe check --machine          one tab-separated line per declaration (for grade.sh) -/

def blocks : List (String × Ochr.Surface.Block) :=
  [("HashMapSpec", HashMapSpec), ("HashMapCompose", HashMapCompose), ("HashMapModel", HashMapModel),
   ("HashMapSolution", HashMapSolution), ("HashMapTests", HashMapTests)]

-- The machine's step budget per declaration: ample for every test.
def fuel : Nat := 50000000

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--machine"] =>
    for (n, b) in blocks do
      for r in (run n b {} fuel).rows do
        let (got, msg) := match r.verdict with
          | .accepted => ("accepted", "")
          | .rejected m => ("rejected", m)
        let msg := (msg.replace "\n" " ").replace "\t" " "
        IO.println s!"ROW\t{n}\t{r.name}\t{if r.expectAccept then "accept" else "reject"}\t{got}\t{msg}"
    return 0
  | ["--trace", name] =>
    for (n, b) in blocks do
      let rep := run n b { trace := true } fuel
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
      IO.println (run n b {} fuel).show
    return 0

-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr Ochr.Test

ochr PT3 uses DepFields {
  def TPDrop (k : Word) (c0 : Pos) : Unit := (let c = c0; match c { MkPos(n, h) => (match k { Zero => (n := n; ()), Succ(m) => (), }; let u : Unit = ?; ()), }; ())
  def TPDropK (c0 : Pos) : Unit := (let c = c0; match c { MkPos(n, h) => (match Succ(Zero) { Zero => (n := n; ()), Succ(m) => (), }; let u : Unit = ?; ()), }; ())
}
def ppHole (name : String) : String :=
  let r := Ochr.Test.runWith (some Prelude) "PT3" PT3 (located := true)
  match r.rows.find? (·.name == name) with
  | some row => String.intercalate "\n" (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (String.intercalate ", " (Ω.map fun (x, T, v) => s!"{x} : {(T.map Value.pp).getD "?"} = {v.pp}"))
      | _ => none)
  | none => "none"
#eval IO.println (ppHole "TPDrop")
#eval IO.println (ppHole "TPDropK")

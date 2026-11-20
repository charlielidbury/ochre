-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr Ochr.Test

ochr PE uses DepFields {
  def NU (b : Word) : Type := match b { Zero => Nat, Succ(m) => Unit, }
  inductive DP := MkDP(b : Word, x : NU(b))
  def S1 : Nat := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let u : Unit = ?; let y = x; y), })
  def S2 (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; let u : Unit = ?; n := Succ(Zero)), })
  def S3 (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; n := Zero; let u : Unit = ?; n := Succ(Zero); h := h0), }
  def S4 (v : &V) : Unit := match *v { MkV(n, x) => (let r = &n; let y = clone(x); let u : Unit = ?; ()), }
  def S5 (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (let r = &n; *r := Zero; let u : Unit = ?; ()), }; ())
}

def ppHole (name : String) : String :=
  let r := Ochr.Test.runWith (some Prelude) "PE" PE (located := true)
  match r.rows.find? (·.name == name) with
  | some row => String.intercalate "\n" (row.trace.toList.filterMap fun
      | .note _ _ (.hole G Ω) => some (s!"goal {G.pp}; Ω: " ++ String.intercalate ", " (Ω.map fun (x, T, v) => s!"{x} : {(T.map Value.pp).getD "?"} = {v.pp}"))
      | _ => none)
  | none => "none"
#eval IO.println (ppHole "S1")
#eval IO.println (ppHole "S2")
#eval IO.println (ppHole "S3")
#eval IO.println (ppHole "S4")
#eval IO.println (ppHole "S5")

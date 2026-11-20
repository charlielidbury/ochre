-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr Ochr.Test

ochr PI uses DepFields {
  def I1 (v : &V) : Word := match *v { MkV(n, x) => (let old = x; let w = Zero; x := &w; let u : Unit = ?; let k = w; *x := Succ(Zero); x := old; k), }
  def I2 (v : &V) : Word := match *v { MkV(n, x) => (let old = x; let w = Zero; x := &w; let k = w; *x := Succ(Zero); x := old; k), }
  def I2c : Word := (let c = One1; I2(&c))
  def I2z : Eq(Word, I2c, Zero) := refl
  def I2s : Eq(Word, I2c, Succ(Zero)) := refl
  def I3 (v : &V) : Word := match *v { MkV(n, x) => (let old = x; let w = Zero; x := &w; *x := Succ(Zero); x := old; w), }
  def I3c : Word := (let c = One1; I3(&c))
  def I3z : Eq(Word, I3c, Zero) := refl
  def I3s : Eq(Word, I3c, Succ(Zero)) := refl
  def I4 (v : &V) : Word := match *v { MkV(n, x) => (let old = x; let w = Zero; x := &w; let r = &w; *r := Succ(Succ(Zero)); *x := Succ(Zero); x := old; w), }
  def I4c : Word := (let c = One1; I4(&c))
  def I4a : Eq(Word, I4c, Succ(Zero)) := refl
  def I4b : Eq(Word, I4c, Succ(Succ(Zero))) := refl
}

def ppHole (name : String) : String :=
  let r := Ochr.Test.runWith (some Prelude) "PI" PI (located := true)
  match r.rows.find? (·.name == name) with
  | some row => String.intercalate "\n" (row.trace.toList.filterMap fun
      | .note _ _ (.hole G Ω) => some (s!"goal {G.pp}; Ω: " ++ String.intercalate ", " (Ω.map fun (x, T, v) => s!"{x} : {(T.map Value.pp).getD "?"} = {v.pp}"))
      | _ => none)
  | none => "none"
#eval IO.println (ppHole "I1")

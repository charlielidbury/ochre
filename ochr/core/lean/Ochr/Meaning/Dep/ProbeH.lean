-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr.Test

ochr PH uses DepFields {
  def H1 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := Nat; let T = x; x := old), }
  def H2 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; let w = Zero; x := &w; x := old), }
  def H3 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := refl; x := old), }
  def H4 (v : &V) : Nat := match *v { MkV(n, x) => (let old = x; x := Nat; let T = x; let k : T = 3; x := old; k), }
  def H5 : Eq(Nat, (let c = One1; H4(&c)), 3) := refl
}

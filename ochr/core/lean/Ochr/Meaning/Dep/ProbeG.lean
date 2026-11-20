-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr.Test

ochr PG uses DepFields {
  -- a leaf written by strong update into a field declared at a data type
  def W1 : Nat := (let c = One1; match c { MkV(n, x) => (x := 5; let y = x; x := O; y), })
  def W1r : Eq(Nat, W1, 5) := refl
  def W2 (c0 : V) : Nat := (let c = c0; match c { MkV(n, x) => (x := 5; let y = x; n := Succ(Zero); x := O; y), })
  def W3 (v : &V) : Unit := match *v { MkV(n, x) => (let old = x; x := (); x := old), }
  def W4 (v : &V) : Unit := match *v { MkV(n, x) => (x := (λ(z : Nat) : Nat => z); ()), }
}

-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Test
open Ochr.Test

ochr Inert {
  inductive One := O
  def F (n : Nat) : Type := match n { Z => One, S(m) => One, }
  inductive V := MkV(n : Nat, x : F(n))
  -- a borrow written into a data field: its loan is never found again, and the constant's value is that loan
  def Leak : Nat := (let c = MkV(Z, O); match c { MkV(n, x) => (let w = Z; x := &w; *x := S(Z); x := O; w), })
  def LeakZ : Eq(Nat, Leak, Z) := refl
  def LeakS : Eq(Nat, Leak, S(Z)) := refl
}
#eval IO.println (run "Inert" Inert).show

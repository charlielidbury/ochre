-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Test
open Ochr.Test

ochr Boom {
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive V := MkV(n : Nat, x : Fin1(n))
  def Bad : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (x := refl; n := Z; let z : Void = match x {}; z), })
  def AbsurdV (v : Void) : False := match v {}
  def BoomF : False := AbsurdV(Bad)
  -- control 1: without `x := refl`, rejected
  def Ctl1 : Void := (let c = MkV(S(Z), O); match c { MkV(n, x) => (n := Z; let z : Void = match x {}; z), })
  -- control 2: an ordinary wrong program, rejected
  def Ctl2 : Void := O
}
#eval IO.println (run "Boom" Boom).show

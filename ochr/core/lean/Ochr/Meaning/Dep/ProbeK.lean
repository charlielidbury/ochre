-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr.Test

ochr PK uses DepFields {
  def K1 : False := (let c = One1; match c { MkV(n, x) => (x := refl; n := Zero; let z : False = match x {}; z), })
  def K2 : False := (let c = One1; match c { MkV(n, x) => (n := Zero; x := refl; let z : False = match x {}; z), })
  def K3 (v : &V) : False := match *v { MkV(n, x) => (let old = x; x := refl; n := Zero; let z : False = match x {}; z), }
  -- control: the same without the proof written in
  def K1Ctl : False := (let c = One1; match c { MkV(n, x) => (n := Zero; let z : False = match x {}; z), })
}

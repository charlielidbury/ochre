-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr.Test

ochr PC uses DepFields {
  inductive Tag (n : Word) := MkTag(h : IsSucc(n))
  inductive TW := MkTW(n : Word, y : Tag(n))
  def Mk1 : Tag(Succ(Zero)) := MkTag(refl)
  def Mk1L : Tag(Succ(Zero)) := (let t = MkTag[Succ(Zero)](refl); t)
  def T1 : IsSucc(Zero) := (let c = MkTW(Succ(Zero), Mk1); match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
  def T2 : IsSucc(Zero) := (let c = MkTW(Succ(Zero), Mk1L); match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
  def T3 : IsSucc(Zero) := (let c = MkTW(Succ(Zero), MkTag[Succ(Zero)](refl)); match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
  def T4 (c0 : TW) : IsSucc(Zero) := (let c = c0; match c { MkTW(n, y) => (n := Zero; match y { MkTag(h) => h, }), })
}

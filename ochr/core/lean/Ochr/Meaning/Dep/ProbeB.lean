-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr.Test

ochr PB uses DepFields {
  def VoidF (z : Void) : False := match z {}
  -- C3: read the dependent field while its index is lent; then write the index through the borrow
  def C3a (v : &V) : False := match *v { MkV(n, x) => (let r = &n; let y = clone(x); *r := Zero; match y {}), }
  def C3b (v : &V) : False := match *v { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); match y {}), }
  def C3c (v : &V) : Unit := match *v { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); n := Succ(Zero); ()), }
  def C3d (c0 : V) : False := (let c = c0; match c { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); match y {}), })
  def C3e (c0 : V) : Void := (let c = c0; match c { MkV(n, x) => (let y = (let r = &n; let y0 = clone(x); *r := Zero; y0); y), })
  -- B1: a positional write of the index, then the proof field read
  def B1 (p0 : Pos) : IsSucc(Zero) := (let p = p0; p.0 := Zero; match p { MkPos(n, h) => h, })
  -- B2: a borrow of the dependent field live while the index is rewritten through another borrow
  def UseVoidRef (y : &Void) : False := match *y {}
  def B2 (c0 : V) : False := (let c = c0; match c { MkV(n, x) => (let rx = &x; let rn = &n; *rn := Zero; UseVoidRef(rx)), })
  def B2b (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (let rx = &x; let rn = &n; *rn := Zero; *rx := O; ()), })
  -- B4: open, then a call with a borrow of the dependent field at the new index's type
  def B4 (c0 : V) : False := (let c = c0; match c { MkV(n, x) => (n := Zero; UseVoidRef(&x)), })
  def UseFin (k : Word) (y : &Fin1(k)) : Unit := ()
  def B4b (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; UseFin(Zero, &x)), })
  def B4c (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (let m = clone(n); n := Zero; UseFin(m, &x); n := m), })
  -- B9: into a constructor
  def B9a : V := (let c = One1; match c { MkV(n, x) => (n := Zero; MkV(clone(n), x)), })
  def B9b : V := (let c = One1; match c { MkV(n, x) => (n := Zero; MkV(Succ(Zero), x)), })
  -- B10: equality between open values / open fields
  def B10a (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => n := Zero, }; Eq(V, c, c))
  def B10b (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => (n := Zero; Eq(Void, x, x)), })
  def B10c (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => (n := Zero; Id(Void, x, x)), })
  def B10d (c0 : V) : Prop := (let c = c0; match c { MkV(n, x) => n := Zero, }; Id(V, c, c))
  -- J1: open on one arm of a known match
  def J1 : Word := (let c = One1; match Zero { Zero => (match c { MkV(n, x) => n := Zero, }; ()), Succ(m) => (), }; match c { MkV(n, x) => clone(n), })
  def J1b : False := (let c = One1; match Zero { Zero => (match c { MkV(n, x) => n := Zero, }; ()), Succ(m) => (), }; match c { MkV(n, x) => match x {}, })
  -- recursion: open, recurse with a borrow of the open value
  def RecO (k : Nat) (v : &V) : Unit by k := match k { Z => (), S m => (match *v { MkV(n, x) => n := Zero, }; RecO(m, v)), }
  def RecF (k : Nat) (v : &V) : Unit by k := match k { Z => (), S m => match *v { MkV(n, x) => (n := Zero; RecF(m, v); n := Succ(Zero)), }, }
}

-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr.Test

ochr PD uses DepFields {
  def VoidF (z : Void) : False := match z {}
  -- nested: the inner value's type depends on the outer index
  def VAt (k : Word) : Type := match k { Zero => One, Succ(m) => V, }
  inductive WV := MkWV(k : Word, w : VAt(k))
  def N1 (c0 : WV) : Unit := (let c = c0; match c { MkWV(k, w) => (k := Succ(Zero); ()), })
  def N2 : False := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (k := Zero; match w { MkV(n, x) => (n := Zero; match x {}), }), })
  def N3 : Word := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (match w { MkV(n, x) => n := Zero, }; k := Zero; match w { MkV(n, x) => clone(n), }), })
  def N4 : False := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (match w { MkV(n, x) => n := Zero, }; match w { MkV(n, x) => match x {}, }), })
  def N5 : Unit := (let c = MkWV(Succ(Zero), One1); match c { MkWV(k, w) => (match w { MkV(n, x) => n := Zero, }; let ww = w; ()), })
  -- a proof's fields are locals: write the witness, use the proof at the new witness
  def PS1 (e : ExSucc) : IsSucc(Zero) := match e { WitS(w, h) => (w := Zero; h), }
  -- the proof field assigned while the index is marked lent to a call's returned borrow
  def PickW (k : Word) (a : &Word) (b : &Word) : &Word := match k { Zero => a, Succ(m) => b, }
  def G1 (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(Succ(Zero), &n, &d); h := h0; *r := Zero), }
  def G2 (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(Zero, &n, &d); h := h0; *r := Zero), }
  def G3 (k : Word) (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(k, &n, &d); h := h0; *r := Zero), }
  def G4 (k : Word) (p : &Pos) : Unit := match *p { MkPos(n, h) => (let h0 = h; let d = Succ(Zero); let r = PickW(k, &n, &d); h := h0; ()), }
  -- closure capturing a field of an open value
  def CL1 (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; let f = (λ(u : Unit) : Unit => (let y = x; ())); n := Succ(Zero); ()), })
  def CL2 (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; let f = (λ(u : Unit) : Fin1(Zero) => x); ()), })
  -- a stuck block borrowing the dependent field of an open value
  def SB1 (k : Word) (c0 : V) : Unit := (let c = c0; match c { MkV(n, x) => (n := Zero; match k { Zero => (let r = &x; ()), Succ(m) => (), }; n := clone(n)), })
  def SB2 (k : Word) (v : &V) : Unit := match *v { MkV(n, x) => (let m = clone(n); n := Zero; match k { Zero => (let r = &x; ()), Succ(mm) => (), }; n := m), }
  -- repack after a repair through a borrow
  def RB (v : &V) : Unit := match *v { MkV(n, x) => (let m = clone(n); let r = &n; *r := Zero; *r := m; ()), }
}
ochr PF uses PD {
  def RBc : Word := (let c = One1; RB(&c); VN(c))
  def RBr : Eq(Word, RBc, Succ(Zero)) := refl
  def N3r : Eq(Word, N3, Zero) := refl
  def P1 : Pos := MkPos(Succ(Zero), refl)
  def G1c : Word := (let p = P1; G1(&p); match p { MkPos(n, h) => clone(n), })
  def G1r : Eq(Word, G1c, Succ(Zero)) := refl
  def SB2a : Word := (let c = One1; SB2(Zero, &c); VN(c))
  def SB2b : Word := (let c = One1; SB2(Succ(Zero), &c); VN(c))
  def SB2ar : Eq(Word, SB2a, Succ(Zero)) := refl
  def SB2br : Eq(Word, SB2b, Succ(Zero)) := refl
  def BadCtl : Eq(Word, RBc, Zero) := refl
  def N1c : Word := (let c = MkWV(Zero, O); N1(c); Zero)
}

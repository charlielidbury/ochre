import Ochr.Test
import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test

-- THE EXPERIMENT `exp-obs-detach` (checker13): the theory lane's programs (docs/18 <sec-rd>, <sec-obs>, the fourth and fifth
-- referees), every row a plain `def` so that each rejection prints its reason. Run on main and on
-- this branch under each observation: the printer at the end runs every block under `today` (main's),
-- `c` and `cplus`. Run: `lake env lean --load-dynlib=.lake/build/lib/libochr_Ochr.so <this file>`.

-- the five sites and their twins (<sec-obs-today>, the third and fourth referees)
ochr T13Sites uses Nats, Fixtures {
  def Ctl : Eq(Nat, Z, S(Z)) := refl
  def H (x : &Nat) (e : Id(Unit, *x := 0, *x := 0)) : Unit := ()
  def FJ2 (n : Nat) (x : &Nat) : Unit := match n { Z => (let h : Id(Unit, *x := 0, *x := 0) = refl; ()), S(m) => (), }
  def S1 (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; FJ2(n, &(*r).0); (*r).1 := z; ())
  def S1Z : Unit := S1(Z)
  def S1S : Unit := S1(S(Z))
  def FJ0 (n : Nat) : Unit := match n { Z => (let h : Id(Unit, (), ()) = refl; ()), S(m) => (), }
  def S1u (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).0; FJ0(n); (*r).0 := z; ())
  def S1uZ : Unit := S1u(Z)
  def CallK (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; (*r).0; FJ0(n); (*r).0 := 0; ())
  def UseK : Unit := CallK(Z)
  def UseKS : Unit := CallK(S(Z))
  def CallK2 (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; FJ2(n, &(*r).0); (*r).1 := z; ())
  def UseK2 : Unit := CallK2(Z)
  def UseK2S : Unit := CallK2(S(Z))
  def AAncOk : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; H(&(*r).0, refl); (*r).1 := z; ())
  inductive Bit := B0 | B1
  def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
  inductive TW := MkTW(b : Bit, x : Payload(b), w : Nat)
  def S2 (n : Nat) : Unit := (let t = MkTW(B0, 3, 5); match t { MkTW(b, x, w) => (b := B1; FJ2(n, &w); x := ()), })
  def S2Z : Unit := S2(Z)
  def S2S : Unit := S2(S(Z))
  def CallK3 (n : Nat) : Unit := (let t = MkTW(B0, 3, 5); match t { MkTW(b, x, w) => (b := B1; FJ2(n, &w); x := ()), })
  def UseK3 : Unit := CallK3(Z)
  def OpenCall : Unit := (let t = MkTW(B0, 3, 5); match t { MkTW(b, x, w) => (b := B1; H(&w, refl); x := ()), })
  def OpenCallW : Unit := (let t = MkTW(B0, 3, 5); match t { MkTW(b, x, w) => (b := B1; let r = &w; *r := 0; x := ()), })
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive VW2 := MkVW2(n : Nat, x : Fin1(n), w : Nat)
  def S3 (n : Nat) : Unit := (let t = MkVW2(S(Z), O, 5); let r = &t; match *r { MkVW2(k, x, w) => (k := Z; FJ2(n, &w); k := S(Z)), })
  def S3Z : Unit := S3(Z)
  def S3S : Unit := S3(S(Z))
  def OpenAnc : Unit := (let t = MkVW2(S(Z), O, 5); let r = &t; match *r { MkVW2(n, x, w) => (n := Z; H(&w, refl); n := S(Z)), })
  def PickP (n : Nat) (x : &Pair(Nat, Nat)) (y : &Pair(Nat, Nat)) : &Pair(Nat, Nat) := match n { Z => x, S(m) => y, }
  def S4 (n : Nat) (m : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let q : Pair(Nat, Nat) = Mk(3, 4); let r = PickP(m, &p, &q); *r := Mk(7, 8); let z = (*r).1; FJ2(n, &(*r).0); (*r).1 := z; ())
  def S4Z (m : Nat) : Unit := S4(Z, m)
  def S4S (m : Nat) : Unit := S4(S(Z), m)
  def UseKF (m : Nat) : Unit := S4(Z, m)
  def UseKFNoWrite (m : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let q : Pair(Nat, Nat) = Mk(3, 4); let r = PickP(m, &p, &q); let z = (*r).1; FJ2(Z, &(*r).0); (*r).1 := z; ())
  inductive VV := MkVV(n : Nat, x : Fin1(n))
  def S5 (n : Nat) : Unit := (let t = MkVV(S(Z), O); match t { MkVV(k, x) => (FJ2(n, &k); k := S(Z)), })
  def S5Z : Unit := S5(Z)
  def S5S : Unit := S5(S(Z))
  def H8 (a : &Nat) (e : Id(Unit, *a := 0, *a := 0)) : Unit := ()
  def W8 (a : &Nat) : Unit := (*a := 0)
  def AH8 : Unit := (let t = MkVV(S(Z), O); match t { MkVV(n, x) => (H8(&n, refl); n := S(Z)), })
  def AW8 : Unit := (let t = MkVV(S(Z), O); match t { MkVV(n, x) => (W8(&n); n := S(Z)), })
  def InFrameMoved : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; let h : Id(Unit, (), ()) = refl; (*r).1 := z; ())
  def InFrameMovedNoId : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; (*r).1 := z; ())
}

-- G5 and every attack on it (<sec-rd-attack>); every row ending in False must stay rejected
ochr T13Attacks uses Nats, Fixtures {
  def Ctl : Eq(Nat, Z, S(Z)) := refl
  def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
  def H (x : &Nat) (e : Id(Unit, *x := 0, *x := 0)) : Unit := ()
  def APick (n : Nat) : False := (let a = 0; let b = 0; let r = Pick(n, &a, &b); G5(r, refl))
  def APickZ : False := (let a = 0; let b = 0; let r = Pick(Z, &a, &b); G5(r, refl))
  def APickOk (n : Nat) : Unit := (let a = 0; let b = 0; let r = Pick(n, &a, &b); H(r, refl))
  def APart : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p.0; let z = p.1; G5(r, refl))
  def APartOk : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p.0; let z = p.1; H(r, refl))
  def AAnc : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; G5(&(*r).0, refl))
  def AAncOk : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; let z = (*r).1; H(&(*r).0, refl); (*r).1 := z; ())
  def AAncWhole : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; G5(&(*r).0, refl))
  def AAncWholeOk : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p; H(&(*r).0, refl); ())
  def ATwo : False := (let a = 0; let r1 = &a; let r2 = &*r1; G5(&*r2, refl))
  def ATwoOk : Unit := (let a = 0; let r1 = &a; let r2 = &*r1; H(&*r2, refl); ())
  def AFill (n : Nat) : False := (let a = n; let r = TailM(&a); G5(r, refl))
  def AFill2 (n : Nat) : False := (let a = n; let r1 = TailM(&a); let r2 = TailM(&*r1); G5(r2, refl))
  def AFillOk (n : Nat) : Unit := (let a = n; let r = TailM(&a); H(r, refl))
  def AMoved : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p.0; let q = p; G5(r, refl))
  def AOver : False := (let a = 0; let r = &a; a := 5; G5(r, refl))
  def AOverPart : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p.0; p.1 := 7; G5(r, refl))
  def AMovedThenRefill : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = &p.0; let z = p.1; p.1 := z; G5(r, refl))
  def ASideMoves (x : &Pair(Nat, Nat)) (e : Id(Unit, ((*x).0 := 0; let z = (*x).1; (*x).1 := z), ((*x).0 := 1; let z = (*x).1; (*x).1 := z))) : False := e
  def KF (x : &Nat) (y : &Nat) : &Nat := (let r = TailM(&*x); x := y; r)
  def AKF : False := (let a = 0; let b = 0; G5(KF(&a, &b), refl))
  def AKFn (n : Nat) : False := (let a = n; let b = 0; G5(KF(&a, &b), refl))
  def AKFok (n : Nat) : Unit := (let a = n; let b = 0; H(KF(&a, &b), refl))
  def KG (x : &Nat) : &Nat := (let r = TailM(&*x); *x := 0; r)
  def KH (x : &Nat) (y : &Nat) : &Nat := (let r = TailM(&*x); let s = Pick(Z, r, y); s)
  def AKH (n : Nat) : False := (let a = n; let b = 0; G5(KH(&a, &b), refl))
  def AKHz : False := (let a = 0; let b = 0; G5(KH(&a, &b), refl))
  def KR (x : &Nat) (y : &Nat) : &Nat := (x := y; x)
  def AKRz : False := (let a = 0; let b = 0; G5(KR(&a, &b), refl))
  def AKRn (n : Nat) : False := (let a = n; let b = n; G5(KR(&a, &b), refl))
  def PU (n : Nat) (u : &Unit) (x : &Nat) : &Nat := match n { Z => x, S(m) => x, }
  def APU (n : Nat) : False := (let u = (); let a = 0; G5(PU(n, &u, &a), refl))
  def RB (x : &Pair(Nat, Nat)) : &Nat := (let r = &(*x).0; (*x).1 := 7; r)
  def ARB : False := (let p : Pair(Nat, Nat) = Mk(1, 2); G5(RB(&p), refl))
  def ARBn (n : Nat) : False := (let p : Pair(Nat, Nat) = Mk(n, 2); G5(RB(&p), refl))
  def ARBOk (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(n, 2); H(RB(&p), refl))
  def G6 (x : &Nat) (y : &Nat) (e : Id(Unit, (*x := 0; *y := 1), (*x := 1; *y := 0))) : False := match e { Intro(l, r) => l, }
  def AG6 : False := (let p : Pair(Nat, Nat) = Mk(5, 5); G6(&p.0, &p.1, refl))
  def PP (n : Nat) (x : &Pair(Nat, Nat)) : &Pair(Nat, Nat) := match n { Z => x, S(m) => x, }
  def AG6F (n : Nat) : False := (let p : Pair(Nat, Nat) = Mk(5, 5); let r = PP(n, &p); G6(&(*r).0, &(*r).1, refl))
  def APT (n : Nat) (m : Nat) : False := (let a = clone(m); let b = m; let r1 = Pick(n, &a, &b); let r2 = TailM(r1); G5(r2, refl))
  def APTOk (n : Nat) (m : Nat) : Unit := (let a = clone(m); let b = m; let r1 = Pick(n, &a, &b); let r2 = TailM(r1); H(r2, refl))
  -- D44's Q and D137's QU family: a borrow with no site, or whose Unit fill eta would drop
  def Q (g : Π(n : Nat). &Nat) : False := G5(g(5), refl)
  def QU (g : Π(u : &Unit). &Nat) : False := (let u = (); G5(g(&u), refl))
  def QU2 (g : Π(u : &Unit) (v : &Unit). &Nat) : False := (let u = (); let v = (); G5(g(&u, &v), refl))
  def QU3 (g : Π(u : &Unit). &Nat) (u : &Unit) : False := G5(g(u), refl)
  def QU4 (g : Π(u : &Unit). &Nat) : False := (let u : Unit = (); G5(g(&u), refl))
  def QU5 (g : Π(u : &Unit). &Nat) (w : Unit) : False := (let u = w; G5(g(&u), refl))
  def UU (n : Nat) : Type := match n { Z => Unit, S(m) => Unit, }
  def QU6 (g : Π(u : &UU(Z)). &Nat) (w : UU(Z)) : False := (let u = w; G5(g(&u), refl))
  def QUp (g : Π(u : &Unit). &Nat) : False := (let p : Pair(Unit, Nat) = Mk((), 0); G5(g(&p.0), refl))
  def QUN (g : Π(u : &Unit) (v : &Nat). &Nat) : False := (let u = (); let v = 0; G5(g(&u, &v), refl))
  def IU1 (u : &Unit) : &Nat := (let a = 0; &a)
}

-- a proof's data field as a lender (PEx), and the field-type attacks
ochr T13Proof uses Nats {
  def Ctl : Eq(Nat, Z, S(Z)) := refl
  def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
  def G5T (x : &Nat) : Prop := Id(Unit, *x := 0, *x := 1)
  def H (x : &Nat) (e : Id(Unit, *x := 0, *x := 0)) : Unit := ()
  inductive Ex : Prop := Wit(w : Nat, h : Eq(Nat, w, w))
  def PEx (e : Ex) : False := match e { Wit(w, h) => G5(&w, refl), }
  def PExOk (e : Ex) : Unit := (let k : Eq(Nat, Z, Z) = match e { Wit(w, h) => (let u = H(&w, refl); refl), }; ())
  def PExId (e : Ex) : False := match e { Wit(w, h) => (let r = &w; let q : Id(Unit, *r := 0, *r := 1) = refl; q), }
  def PExT (e : Ex) : True := match e { Wit(w, h) => (let t : Prop = G5T(&w); let q : Eq(Prop, t, False) = refl; refl), }
  def PExF (e : Ex) : True := match e { Wit(w, h) => (let t : Prop = G5T(&w); let f = (λ(k : t) : Eq(Nat, Z, S(Z)) => match k {}); refl), }
  inductive Bit := B0 | B1
  def Payload (b : Bit) : Type := match b { B0 => Nat, B1 => Unit, }
  inductive Tagged := MkT(b : Bit, x : Payload(b))
  def GB (x : &Bit) (e : Id(Unit, *x := B0, *x := B1)) : False := e
  def ATagIdx : False := (let t = MkT(B0, 3); match t { MkT(b, x) => GB(&b, refl), })
  def ATagIdx2 (t0 : Tagged) : False := (let t = t0; match t { MkT(b, x) => GB(&b, refl), })
  def ATagLeaf : False := (let t = MkT(B0, 3); match t { MkT(b, x) => G5(&x, refl), })
  def ATagLeaf2 (t0 : Tagged) : False := (let t = t0; match t { MkT(b, x) => match b { B0 => G5(&x, refl), B1 => G5(&x, refl), }, })
}

-- the fourth referee's F1 (Bad must stay rejected), and the fill-site twins
ochr T13F1 uses Nats {
  def Ctl : Eq(Nat, Z, S(Z)) := refl
  def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
  def G5T (x : &Nat) : Prop := Id(Unit, *x := 0, *x := 1)
  def H (x : &Nat) (e : Id(Unit, *x := 0, *x := 0)) : Unit := ()
  def PP (n : Nat) (x : &Pair(Nat, Nat)) : &Pair(Nat, Nat) := match n { Z => x, S(m) => x, }
  def CallF (n : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = PP(n, &p); let z = (*r).1; H(&(*r).0, refl); (*r).1 := z; ())
  def CallFZ : Unit := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = PP(Z, &p); let z = (*r).1; H(&(*r).0, refl); (*r).1 := z; ())
  def Bad (n : Nat) (e : (let p : Pair(Nat, Nat) = Mk(1, 2); let r = PP(n, &p); let z = (*r).1; let T = G5T(&(*r).0); (*r).1 := z; T)) : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = PP(n, &p); let z = (*r).1; let res = G5(&(*r).0, e); (*r).1 := z; res)
  def BadW (n : Nat) (e : (let p : Pair(Nat, Nat) = Mk(1, 2); let r = PP(n, &p); G5T(&(*r).0))) : False := (let p : Pair(Nat, Nat) = Mk(1, 2); let r = PP(n, &p); G5(&(*r).0, e))
  def BadZ : False := Bad(Z, refl)
  def BadWZ : False := BadW(Z, refl)
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive VW := MkVW(n : Nat, x : Fin1(n), w : Nat)
  def PV (k : Nat) (x : &VW) : &VW := match k { Z => x, S(m) => x, }
  def CallO (k : Nat) : Unit := (let t = MkVW(S(Z), O, 5); let r = PV(k, &t); match *r { MkVW(n, x, w) => (let n0 = clone(n); n := Z; H(&w, refl); n := n0), })
}

-- the own check's forms, the lost equations, induction hypotheses, the block residue, the order of conjuncts
ochr T13Forms uses Nats, Fixtures {
  def Ctl : Eq(Nat, Z, S(Z)) := refl
  def OwnR (x : &Nat) : Unit := (let r = TailM(x); let h : Id(Unit, *r := 0, *r := 1) = refl; ())
  def OwnRx (x : &Nat) : Unit := (let r = TailM(&*x); let h : Id(Unit, *r := 0, *r := 1) = refl; ())
  def OwnRF (x : &Nat) : Unit := (let r = TailM(x); let h : Eq(Prop, Id(Unit, *r := 0, *r := 1), False) = refl; ())
  def OwnRxF (x : &Nat) : Unit := (let r = TailM(&*x); let h : Eq(Prop, Id(Unit, *r := 0, *r := 1), False) = refl; ())
  inductive Void : Type
  inductive One := O
  def Fin1 (n : Nat) : Type := match n { Z => Void, S(m) => One, }
  inductive VV := MkVV(n : Nat, x : Fin1(n))
  def IdxSame : Unit := (let t = MkVV(S(Z), O); match t { MkVV(k, x) => (let r = &k; let h : Id(Unit, *r := Z, *r := Z) = refl; ()), })
  def IdxDiff : Unit := (let t = MkVV(S(Z), O); match t { MkVV(k, x) => (let r = &k; let q : Eq(Prop, Id(Unit, *r := S(Z), *r := S(S(Z))), False) = refl; ()), })
  def ConsW : Unit := (let a = 0; let r = &a; let h : Id(Unit, (let r2 = r; a := 5), (let r2 = r; *r2 := 7; a := 5)) = refl; ())
  def ConsM : Unit := (let a = 0; let r = &a; let h : Id(Unit, (let r2 = r; let z = a; ()), (let r2 = r; *r2 := 7; let z = a; ())) = refl; ())
  def ConsP (x : &Nat) : Unit := (let h : Id(Unit, (let r2 = x; ()), (let r2 = x; *r2 := 7)) = refl; ())
  def Lift (x : &Nat) : Id(Unit, (let r = TailM(&*x); AddM(&*r, 0)), (let r = TailM(&*x); ())) := (let r = TailM(&*x); AddMZero(r))
  def LiftC (x : &Nat) : Id(Unit, (let r = TailM(&*x); AddM(&*r, 0)), (let r = TailM(&*x); ())) := (let r = TailM(&*x); let c = clone(*r); AddMZero(&c))
  def LiftR (x : &Nat) : Id(Unit, (let r = TailM(&*x); AddM(&*r, 0)), (let r = TailM(&*x); ())) := (let r = TailM(&*x); let c = clone(*r); let h = AddMZero(&c); rewrite ← h in refl)
  def BlkFill (n : Nat) (k : Nat) (a : &Nat) (b : &Nat) : Unit := (let r = Pick(n, &*a, &*b); match k { Z => (let h : Id(Unit, *r := 0, *r := 0) = refl; ()), S(j) => (), }; ())
  def UseBlkFill : Eq(Nat, (let c = 3; let d = 4; BlkFill(Z, Z, &c, &d); c), 3) := refl
  def BlkFill1 (n : Nat) (k : Nat) (a : &Nat) (b : &Nat) : Unit := (let r = Pick(n, &*a, &*b); match k { Z => (let h : Id(Unit, *r := 0, *r := 1) = refl; ()), S(j) => (), }; ())
  def G7 (a : Nat) (b : Nat) (x : &Nat) (y : &Nat) (e : Id(Unit, (*x := clone(a); *y := clone(b)), (*x := clone(b); *y := clone(a)))) : Unit := ()
  def G7T (a : Nat) (b : Nat) (x : &Nat) (y : &Nat) : Prop := Id(Unit, (*x := clone(a); *y := clone(b)), (*x := clone(b); *y := clone(a)))
  def OwnForm (a : Nat) (b : Nat) (x : &Nat) (y : &Nat) : Unit := (let t : Prop = G7T(clone(a), clone(b), x, y); let q : Eq(Prop, t, Eq(Nat, a, b) ∧ Eq(Nat, b, a)) = refl; ())
  def SwapForm2 (a : Nat) (b : Nat) : Unit := (let p : Pair(Nat, Nat) = Mk(5, 5); let t : Prop = G7T(clone(a), clone(b), &p.1, &p.0); let q : Eq(Prop, t, Eq(Nat, b, a) ∧ Eq(Nat, a, b)) = refl; ())
  def SwapCall2 (a : Nat) (b : Nat) (e : Eq(Nat, a, b) ∧ Eq(Nat, b, a)) : Unit := (let p : Pair(Nat, Nat) = Mk(5, 5); G7(clone(a), clone(b), &p.1, &p.0, e))
  def SwapCall2Ok (a : Nat) (b : Nat) (e : Eq(Nat, b, a) ∧ Eq(Nat, a, b)) : Unit := (let p : Pair(Nat, Nat) = Mk(5, 5); G7(clone(a), clone(b), &p.1, &p.0, e))
}

def T13blocks : List (String × Ochr.Surface.Block) :=
  [("T13Sites", T13Sites), ("T13Attacks", T13Attacks), ("T13Proof", T13Proof), ("T13F1", T13F1), ("T13Forms", T13Forms)]

def T13show : Ochr.Verdict → String
  | .accepted => "accepted"
  | .rejected m _ => s!"rejected: {m}"
  | .undecided m => "undecided: " ++ m

#eval show IO Unit from do
  for (n, b) in T13blocks do
    let rs := [Ochr.ObsDetach.today, .c, .cplus].map fun m => (Ochr.Test.run n b { obsDetach := m }).rows
    match rs with
    | [r0, r1, r2] =>
      for ((a, b'), c) in (r0.zip r1).zip r2 do
        let vs := [T13show a.verdict, T13show b'.verdict, T13show c.verdict]
        let tag := if vs.all (· == T13show a.verdict) then "same" else "DIFF"
        IO.println s!"{tag} {n}.{a.name}
  today: {T13show a.verdict}
  (C):   {T13show b'.verdict}
  (C+):  {T13show c.verdict}"
    | _ => pure ()

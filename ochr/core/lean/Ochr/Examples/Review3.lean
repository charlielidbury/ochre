import Ochr.Examples.Logic

/-! # reviewer-3 (DECISIONS D48): borrows of data only, only at the top of declared types

The reviewer's probes (S2, S7, S8, S10) as regressions. Before D48, `&T : Type₀` for
every `T` made `Type₀` impredicative (`Π(x : &Type)(a : *x). *x : Type`, the polymorphic
identity applied to itself), which puts System U⁻ (Hurkens' paradox) inside the rules and
breaks the set model; and a codomain that *computed* to `&Nat` took [Close]'s data row at
the generic call but returned a live borrow at an instance, so an accepted `G` read `⊥`. -/

open Ochr.Test

ochr D48 {
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  -- (1) only data is borrowed: not a universe (S8, S2) ...
  reject def Impred : Type := Π(x : &Type) (a : *x). *x
  reject def PolyId (x : &Type) (a : *x) : *x := a
  reject def SelfApp (u : Unit) : Impred := let T = Impred; PolyId(&T, PolyId)
  reject def SelfAppEq (n : Nat) : Id Nat (let T = Impred; let f = PolyId(&T, PolyId); let N = Nat; f(&N, n)) n := refl
  reject def PolyTy : Type := Π(x : &Type) (a : Nat). Nat
  -- ... not a proposition (S10) or a universe of propositions, not a Π-type, not a type variable
  reject def PIref (x : &Prop) (h1 : *x) (h2 : *x) : Id (*x) h1 h2 := refl
  reject def RefTrue (x : &True) : Nat := 0
  reject def RefFun (f : &(Π(n : Nat). Nat)) : Nat := 0
  reject def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()
  -- data is: Nat, Unit, ×, inductive types in Type (at any parameters)
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  def RefList (A : Type) (xs : &List(A)) : Unit := ()
  def RefPair (p : &(Nat × Unit)) : Unit := *p := (0, ())
  -- (2) & only at the top of a declared type (S7): a codomain that computes to &Nat ...
  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat | S _ => Nat }) := match n { Z => x | S _ => 0 }
  reject def G (n : Nat) (a : Nat) : Nat := let r = F(n, &a); let r2 = r; let r3 = r; a
  reject def UseG : Nat := G(0, 5)
  -- ... or & inside another type
  reject def InPair (p : Nat × &Nat) : Nat := 0
  reject def InId (x : &Nat) (h : Id (&Nat) x x) : Nat := 0
  -- at the top of a parameter, a result, an annotation, and a Π-type's parts: fine
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x | S p => TailM(&p) }
  def Ann (x : &Nat) : Unit := let r : &Nat = TailM(x); *r := 1
  def HO (f : Π(x : &Nat). &Nat) (y : &Nat) : Unit := let r = f(y); *r := 2
}

#eval IO.println (run "D48" D48).show

-- every verdict as expected, and exactly 21 assertions (a truncated file changes the count)
#guard (run "D48" D48).allAsExpected
#guard (run "D48" D48).count == 21

/-! ## D49 (clarifications of v2.0's matching on proofs) and D50 -/

ochr D49 {
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤ | S a' => match b { Z => False | S b' => Le(a', b') } }
  -- (1) a proof scrutinee's type is its stored type as refined by [Split]: here Le(S q, 0),
  -- which normalises to False, so the impossible case is a match with no arms
  def SubM (x : &Nat) (y : Nat) (h : Le(y, *x)) : Unit by y :=
    match y { Z => () | S q => match *x { Z => match h {} | S p => *x := p; SubM(x, q, h) } }
  -- ... and a type still neutral there is a type error (fail-safe)
  reject def Neutral (a : Nat) (b : Nat) (h : Le(a, b)) : Nat := match h {}
  -- (3) a data field of a proof is a fresh abstract value (so it can be split), a proof
  -- field is ⋆
  inductive Sq : Prop := Mk(n : Nat)
  def SqSplit (h : Sq) : True := match h { Mk(n) => match n { Z => refl | S m => refl } }
  reject def SqZero (h : Sq) : Id Nat 0 0 := match h { Mk(n) => (refl : Id Nat n 0) }
  -- (4) constructors take their parameters first (surface C[ā](t̄)), and values record them,
  -- so a captured value built from an argument-less constructor has a type
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  def Explicit : List(Nat) := Cons[Nat](1, Nil[Nat])
  reject def ExplicitWrong : List(Nat) := Cons[Unit](1, Nil[Unit])
  def PairP (P : Prop) (Q : Prop) (h : P) (k : Q) : P ∧ Q := Intro[P, Q](h, k)
  def CapNil (u : Unit) : Nat := let xs = Nil[Nat]; let f = (λ(n : Nat) : List(Nat) => xs); 0
  def CapNilAnn (u : Unit) : Nat := let xs : List(Nat) = Nil; let f = (λ(n : Nat) : List(Nat) => xs); 0
}

#eval IO.println (run "D49" D49).show

-- every verdict as expected, and exactly 13 assertions (a truncated file changes the count)
#guard (run "D49" D49).allAsExpected
#guard (run "D49" D49).count == 13

/-! ## D48 (3): Π-types compared under their binders (reviewer-3 C3, probes S3, S9) -/

ochr PiConv {
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  -- a closure that captures a variable has a closed Π-type
  def Apply (f : Π(n : Nat). Nat) (n : Nat) : Nat := f(n)
  def Cap (m : Nat) : Nat := Apply(λ(n : Nat) : Nat => Add(n, m), 0)
  def CapEq (m : Nat) : Id Nat (Apply(λ(n : Nat) : Nat => Add(n, m), 0)) (Add(0, m)) := refl
  -- type abbreviations unfold under binders
  def Pow (X : Type) : Type := Π(a : X). Prop
  def P1 : Pow(Nat) := λ(a : Nat) : Prop => ⊤
  def UseP (p : Pow(Nat)) : Prop := p(0)
  def P3 (u : Unit) : Prop := UseP(λ(a : Nat) : Prop => ⊤)
  -- lemma statements are compared by what they compute to
  def ZeroAdd (n : Nat) : Id Nat (Add(0, n)) n := refl
  def UseRefl (h : Π(n : Nat). Id Nat n n) : Unit := ()
  def PassZeroAdd (u : Unit) : Unit := UseRefl(ZeroAdd)
  -- under a borrow binder, one generic owner serves both sides
  def UseA (h : Π(x : &Nat). Id Unit (AddM(x, 0)) ()) : Unit := ()
  def PassA (h : Π(y : &Nat). Id Unit (let t = 0; AddM(y, t)) ()) : Unit := UseA(h)
  -- statements that differ at the generic arguments stay different
  reject def PassStuck (h : Π(n : Nat). Id Nat (Add(n, 0)) n) : Unit := UseRefl(h)
  reject def PassWrong (h : Π(n : Nat). Id Nat n 0) : Unit := UseRefl(h)
  def UseW (h : Π(x : &Nat). Id Unit (*x := 0) (*x := 0)) : Unit := ()
  reject def PassW (h : Π(x : &Nat). Id Unit (*x := 0) (*x := 1)) : Unit := UseW(h)
  reject def PassDom (f : Π(n : Unit). Nat) : Nat := Apply(f, 0)
}

#eval IO.println (run "PiConv" PiConv).show

-- every verdict as expected, and exactly 19 assertions (a truncated file changes the count)
#guard (run "PiConv" PiConv).allAsExpected
#guard (run "PiConv" PiConv).count == 19

/-! ## ∧-elimination by matching on And (reviewer-3 C4, probe S6) -/

ochr AndElim {
  def AndL (P : Prop) (Q : Prop) (h : P ∧ Q) : P := match h { Intro(a, b) => a }
  def AndL2 (a : Nat) (b : Nat) (h : Eq Nat a 0 ∧ Eq Nat b 0) : Eq Nat a 0 := match h { Intro(l, r) => l }
  -- an Id over two owners computes to a conjunction, taken apart by a match
  def Two (x : &Nat) (y : &Nat) (h : Id Unit (*x := 0; *y := 0) ()) : Eq Nat 0 *x := match h { Intro(l, r) => l }
  def TwoR (x : &Nat) (y : &Nat) (h : Id Unit (*x := 0; *y := 0) ()) : Eq Nat 0 *y := match h { Intro(l, r) => r }
  reject def TwoWrong (x : &Nat) (y : &Nat) (h : Id Unit (*x := 0; *y := 0) ()) : Eq Nat 0 *y := match h { Intro(l, r) => l }
  def Three (x : &Nat) (y : &Nat) (z : &Nat) (h : Id Unit (*x := 0; *y := 0; *z := 0) ()) : Eq Nat 0 *z :=
    match h { Intro(l, r) => match r { Intro(m, n) => n } }
  -- there is no projection on proofs (a proof is ⋆): match instead
  reject def Proj (P : Prop) (Q : Prop) (h : P ∧ Q) : P := h.1
}

#eval IO.println (run "AndElim" AndElim).show

-- every verdict as expected, and exactly 7 assertions (a truncated file changes the count)
#guard (run "AndElim" AndElim).allAsExpected
#guard (run "AndElim" AndElim).count == 7

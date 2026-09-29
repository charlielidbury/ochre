import Ochr.Examples.V17

/-! # Rules v1.7–v1.8 regressions: breaker-fresh-v16 X1–X5, D36, and finding P3

X1/X2 are further forms of BoomL/BoomB (D35). X3 is a generalisation escaping a private
copy (D37), X4 D30 on borrow results (D38), X5 a re-closing loop (D39). `Positivity` holds the
formal appendix's positivity attack (D36). The ledger is in Registry.lean. -/

open Ochr.Test

ochr V18 {
  def U (n : Nat) : Type := match n { Z => Prop, S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤, S _ => ⊤ }

  -- X1: a closure made by a top-level function, with codomain U(n) over a captured n
  def Mk (n : Nat) : (Π(x : &Nat). U(n)) := λ(x : &Nat) : U(n) => (*x := S Z; V(n))
  def Lie8 (n : Nat) : Id Nat (let c = Z; let g = Mk(n); g(&c); c) (S Z) := refl
  reject def Boom8 : Eq Nat Z (S Z) := Lie8(Z)
  reject def Direct8 : Id Nat (let c = Z; let g = Mk(0); g(&c); c) Z := refl

  -- X2: an annotated type-valued match; neither the block nor the inline match is a
  -- proof (its type Prop has sort Type₀), so the write is kept on both paths
  reject def Lie7 (n : Nat) : Id Nat (let c = Z; let T : Prop = match n { Z => (c := S Z; ⊤), S _ => (c := S Z; ⊤) }; c) Z := refl
  reject def Boom7 : Eq Nat (S Z) Z := Lie7(Z)
  reject def P3d (n : Nat) : Nat :=
    let c = Z; let T : Nat = match n { Z => (c := S Z; 0), S _ => (c := S Z; 0) }; let h : Id Nat c Z = refl; c

  -- X3: a generalisation made while forming the goal (a private copy) names σ_g; the
  -- body's split must not be issued the same name (D37)
  inductive Box := MkBox(x : Nat)
  def Double (n : Nat) : Nat by n := match n { Z => Z, S p => S (S (Double(p))) }
  reject def Esc (n : Nat) (m : Box) :
    Id Nat (let b = Double(n); match b { Z => 0, S _ => 1 }) (match m { MkBox(x) => match x { Z => 0, S _ => 1 } }) :=
    match m { MkBox(x) => match x { Z => refl, S _ => refl } }
  reject def BoomE : Eq Nat 1 0 := Esc(1, MkBox(0))

  -- X4: functions returning borrows into different arguments are not convertible (D38)
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y
  reject def ConvPick : Eq (Π(x : &Nat) (y : &Nat). &Nat) PickX PickY := refl
  def Q (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := Π(x : &Nat) (y : &Nat). Id Unit (let r = h(x, y); *r := S Z) (*x := S Z)
  def TX : Q(PickX) := let h = PickX; (λ(x : &Nat) (y : &Nat) : Id Unit (let r = h(x, y); *r := S Z) (*x := S Z) => refl)
  reject def TY : Q(PickY) := J(Π(x : &Nat) (y : &Nat). &Nat, PickX, PickY, Q, refl, TX)
  reject def BoomX4 : (Eq Nat 0 1) ∧ (Eq Nat 1 0) := let c = Z; let d = Z; TY(&c, &d)

  -- X5: an abstract borrow-returning call with two borrow arguments, then a read of an
  -- owner: terminates (D39)
  def P1 (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := Id Nat (let a = Z; let b = Z; (let r = h(&a, &b); ()); a) Z

  -- P3 (this checker, found implementing v1.8): P1's fix read "a place is a proof" off
  -- its value ⋆, but g(0) (data by syntax, codomain V(Z)) is ⋆ at an instance and a
  -- sealed program at the generic call. A variable is a proof iff it is declared so.
  def LieH (g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let h = g(0); (c := S Z; h); c) (S Z) := refl
  reject def BoomH : Eq Nat Z (S Z) := LieH((λ(y : Nat) : V(Z) => refl))
}

-- D36: strict positivity (formal appendix note 3)
ochr Positivity {
  inductive Empty := E(e : Empty)
  def absurd (e : Empty) : False by e := match e { E(e') => absurd(e') }
  reject inductive Bad := Mk(f : Π(x : Bad). Empty)
  reject def L (b : Bad) : Empty := match b { Mk(f) => f(b) }
  reject def K (b : Bad) : False := absurd(L(b))
  reject def bad : Bad := Mk(λ(x : Bad) : Empty => L(x))
  reject def Boom : False := K(bad)
  -- first-order fields are fine
  inductive Pairs := PNil | PCons(hd : Nat × Unit, tl : Pairs)
}

#eval IO.println (run "V18" V18).show
#eval IO.println (run "Positivity" Positivity).show

-- every verdict as expected, and exactly 23 + 8 assertions (a truncated file changes the count)
#guard (run "V18" V18).allAsExpected
#guard (run "V18" V18).count == 23
#guard (run "Positivity" Positivity).allAsExpected
#guard (run "Positivity" Positivity).count == 8

-- A generalised σ has the matched place's type (v1.8, formal appendix [Split-gen]): here
-- a loan fill ⌈let c1 = σ; AppendM(&c1, Nil); c1⌉, whose head gave no type (v1.6: Nat)
ochr GenTy {
  inductive List := Nil | Cons(h : Nat, t : List)
  def AppendM (xs : &List) (ys : List) : Unit by xs := match *xs { Nil => *xs := ys, Cons(h, t) => AppendM(&t, ys) }
  def GenL (xs : List) : Nat := let l = xs; AppendM(&l, Nil); match l { Nil => 0, Cons(h, t) => 1 }
}

def genTrace (cfg : Ochr.Config) : String := (run "GenTy" GenTy { cfg with trace := true }).showTrace "GenL"
#guard (run "GenTy" GenTy).allAsExpected
#guard ((genTrace {}).splitOn "c1⌉ to σ1 : List").length == 2
#guard ((genTrace { genPlaceType := false }).splitOn "c1⌉ to σ1 : Nat").length == 2

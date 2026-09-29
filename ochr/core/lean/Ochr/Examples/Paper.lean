import Ochr.Examples.Review3

/-! # The paper's printed programs that no other test states verbatim

Every program the paper prints is checked by the suite (the table in
`notes/lean-checker.md` §16 maps each one to its test). Most are tested under their own
names elsewhere; this file holds the rest, as printed, up to the surface syntax (`λ` and
`Π` in a `let` need parentheses; `Type₀` is written `Type`; subscripts are digits). -/

open Ochr.Test

ochr Paper {
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y, S p => AddM(&p, y) }
  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x := match *x { Z => refl, S p => AddMZero(&p) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  -- §2: `Id Nat (Add(2, 3)) 5` holds by refl
  def Add23 : Id Nat (Add(2, 3)) 5 := refl
  -- §2: an induction hypothesis about a copy of the predecessor lacks the successor
  reject def AddZeroCopy (x : Nat) : Id Nat (Add(x, 0)) x by x := match x { Z => refl, S p => AddZeroCopy(p) }
  -- §4: `Id Nat (Add(x, x)) x` must be a well-formed statement
  def AddXX (x : Nat) : Prop := Id Nat (Add(x, x)) x
  -- Fig. 7: universes are not cumulative (a proposition is not a type in Type₀; Prop is one)
  reject def NonCumul (P : Prop) : Type := P
  def PropInType : Type := Prop
  -- §6: after `let z = (let y = &x; *y := 2; x)`, `Id Nat z 2` holds by refl
  def LetZ (x : Nat) : Nat := let z = (let y = &x; *y := 2; x); let h : Id Nat z 2 = refl; z
  -- §6: `λ(x : &Nat). (*x := 5; refl)` does not have type `Π(x : &Nat). Id Nat (*x) 5`
  reject def LamWrite : (Π(x : &Nat). Id Nat (*x) 5) := λ(x : &Nat) : Id Nat (*x) 5 => (*x := 5; refl)
  -- §5: owned locals are observed: `x := 6` and `()` differ in what they leave in x
  reject def OwnedLocal (x : Nat) : Id Unit (x := 6) () := refl
  def OwnedLocalNeq (x : Nat) (h : Id Unit (x := 6) ()) : Eq Nat 6 x := h
  -- §5: `Id Unit (*x := 0) (*x := 1)` computes to False, and `match e {}` eliminates it
  def WriteNeq (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Nat := match e {}
  -- §7: naturality only up to resolution: rejected symbolically, accepted at each instance
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x, S _ => y }
  reject def PickEarly (n : Nat) (a : Nat) (b : Nat) : Unit :=
    let r = Pick(n, &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly0 (a : Nat) (b : Nat) : Unit :=
    let n = 0; let r = Pick(n, &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly1 (a : Nat) (b : Nat) : Unit :=
    let n = 1; let r = Pick(n, &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  -- §9: borrows stored in data are outside the core
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  reject def IterM (xs : &List(Nat)) : List(&Nat) := Nil
  -- §9 (reviewer-3 S4): every function of type Π(x : &Nat). &Nat has an injective backward function
  def L (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e
  def Inj (g : Π(x : &Nat). &Nat) (x : &Nat) (e : Id Unit (let r = g(x); *r := 0) (let r = g(x); *r := 1)) : False :=
    let r = g(x); L(r, e)
  -- App. A [T-Ref]: `&Box(Prop)` is a borrow of data
  inductive Box (A : Type) := MkBox(x : A)
  def RefBoxProp (x : &Box(Prop)) : Unit := ()
  -- App. D [Conv-fun]: conversion is least, so two closures stuck at their generic calls
  -- are not identified (coinductively they would be, and J would prove Eq Nat (S Z) Z)
  reject def CoInd : Eq (Π(x : &Nat). Unit) (λ(x : &Nat) : Unit => match *x { Z => (), S _ => *x := Z })
      (λ(x : &Nat) : Unit => match *x { Z => *x := S Z, S _ => () }) := refl
}

#eval IO.println (run "Paper" Paper).show

-- every verdict as expected, and exactly 24 assertions (a truncated file changes the count)
#guard (run "Paper" Paper).allAsExpected
#guard (run "Paper" Paper).count == 24

-- Appendix note 4 and Fig. 7's strict positivity, as printed (with False)
ochr Note4 {
  reject inductive Bad := Mk(f : Π(x : Bad). False)
  reject def L (b : Bad) : False := match b { Mk(f) => f(b) }
  reject def Bad4 : False := L(Mk(λ(x : Bad) : False => L(x)))
}

#eval IO.println (run "Note4" Note4).show

-- every verdict as expected, and exactly 3 assertions (a truncated file changes the count)
#guard (run "Note4" Note4).allAsExpected
#guard (run "Note4" Note4).count == 3

-- Appendix note 5, as printed (V18.Esc is the same program with the constructor MkBox)
ochr Note5 {
  inductive Box := Mk(x : Nat)
  def Double (n : Nat) : Nat by n := match n { Z => Z, S p => S (S (Double(p))) }
  reject def Esc (n : Nat) (m : Box) :
    Id Nat (let b = Double(n); match b { Z => 0, S _ => 1 }) (match m { Mk(x) => match x { Z => 0, S _ => 1 } }) :=
    match m { Mk(x) => match x { Z => refl, S _ => refl } }
  reject def Bad5 : Eq Nat 1 0 := Esc(1, Mk(0))
}

#eval IO.println (run "Note5" Note5).show

-- every verdict as expected, and exactly 4 assertions (a truncated file changes the count)
#guard (run "Note5" Note5).allAsExpected
#guard (run "Note5" Note5).count == 4

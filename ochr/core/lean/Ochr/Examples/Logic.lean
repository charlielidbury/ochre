import Ochr.Examples.D44

/-! # Rules v2.0 (D45–D47): the connectives are inductive definitions

`False`, `True` and `And` are library declarations (`Check.prelude`); `⊤`, `P ∧ Q`,
`⟨h, k⟩` and `refl` are notation. A match on a proof is by its type, large elimination
from a proof needs a subsingleton, and distinct constructors are disjoint in `Eq`.
Programs: `Logic` (ex falso, emptiness, disjointness), `ByType` (matching on proofs, on
both evaluation paths), `OrAttack` (subsingleton elimination), `PList` (a polymorphic
list), `PosParam` (positivity with parameters). -/

open Ochr.Test

ochr Logic {
  -- ex falso: False has no constructors, so a match on a proof of it has no arms and
  -- is well typed at any result type (data, a proposition, an effect-sensitive Id)
  def absurd (h : False) : Nat := match h {}
  def absurdP (P : Prop) (h : False) : P := match h {}
  def absurdId (x : &Nat) (h : False) : Id Unit (*x := 5) () := match h {}
  def absurdLet (h : False) : Nat := let n : Nat = match h {}; S n
  -- False is empty: no closed term has its type
  reject def Bot1 : False := refl
  reject def Bot2 : False := ⟨refl, refl⟩
  reject def Bot3 : False := let h : False = refl; h
  reject def Bot4 : False := absurdP(False, refl)
  -- a match with no arms needs a type with no constructors
  reject def NotEmpty (h : True) : Nat := match h {}
  reject def NotEmptyNat (n : Nat) : Nat := match n {}
  -- D47: distinct constructors are disjoint, so Eq Nat Z (S Z) is False by conversion
  def NoConf (h : Eq Nat Z (S Z)) : False := h
  def NoConfS (n : Nat) (h : Eq Nat Z (S n)) : False := h
  def NoConfMatch (n : Nat) (h : Eq Nat (S n) Z) : Nat := match h {}
  def NoConfBack (h : False) : Eq Nat 0 1 := h
  -- no injectivity (D47): Eq Nat (S a) (S b) does not compute to Eq Nat a b
  reject def Inj (a : Nat) (b : Nat) (h : Eq Nat (S a) (S b)) : Eq Nat a b := h
  -- at a user inductive, and after a write (the observation of Id is disjoint)
  inductive Bool := ff | tt
  def BoolDisj (h : Eq Bool ff tt) : False := h
  def WriteDisj (x : &Nat) (h : Id Unit (*x := 0) (*x := 1)) : False := h
  reject def WriteSame (x : &Nat) (h : Id Unit (*x := 0) (*x := 0)) : False := h
  -- the notation is the library: ⟨h, k⟩ is Intro(h, k), ⊤ is True, refl is I
  def Pair (P : Prop) (Q : Prop) (h : P) (k : Q) : P ∧ Q := ⟨h, k⟩
  def PairI (P : Prop) (Q : Prop) (h : P) (k : Q) : And(P, Q) := Intro(h, k)
  def ReflI : True := I
  def TopUnit (P : Prop) (h : P) : ⊤ ∧ P := h
  reject def AndWrong (P : Prop) (Q : Prop) (h : P) (k : Q) : Q ∧ P := ⟨h, k⟩
  -- large elimination from True and And is allowed (subsingletons)
  def FromTrue (h : True) : Nat := match h { I => 5 }
  def FromTrueIs : Eq Nat (FromTrue(refl)) 5 := refl
}

#eval IO.println (run "Logic" Logic).show

-- every verdict as expected, and exactly 26 assertions (a truncated file changes the count)
#guard (run "Logic" Logic).allAsExpected
#guard (run "Logic" Logic).count == 26

ochr ByType {
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x := match *x { Z => refl | S p => AddMZero(&p) }
  -- a match on a proof is by its type: the arm binds the fields as places holding ⋆
  def Swap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q ∧ P := match h { Intro(a, b) => ⟨b, a⟩ }
  def Fst (P : Prop) (Q : Prop) (h : P ∧ Q) : P := match h { Intro(a, b) => a }
  reject def FstWrong (P : Prop) (Q : Prop) (h : P ∧ Q) : Q := match h { Intro(a, b) => a }
  def FstSwap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q := Fst(Q, P, Swap(P, Q, h))
  -- large elimination from And (its fields are propositions): data from a proof
  def Two (P : Prop) (Q : Prop) (h : P ∧ Q) : Nat := match h { Intro(a, b) => 2 }
  def TwoIs (P : Prop) (Q : Prop) (h : P ∧ Q) : Eq Nat (Two(P, Q, h)) 2 := refl
  -- ... and an effect: a data function that matches on a proof, then writes
  def WriteIf (x : &Nat) (P : Prop) (Q : Prop) (h : P ∧ Q) : Unit := match h { Intro(a, b) => *x := 7 }
  def WriteIfId (x : &Nat) (P : Prop) (Q : Prop) (h : P ∧ Q) : Id Unit (WriteIf(x, P, Q, h)) (*x := 7) := refl
  reject def WriteIfLie (x : &Nat) (P : Prop) (Q : Prop) (h : P ∧ Q) : Id Unit (WriteIf(x, P, Q, h)) () := refl
  -- two paths: the lemmas were checked at h = ⋆ (generic call); here they are
  -- instantiated at propositions about a mutated place, and the instance statements
  -- are computed by running WriteIf/Two directly
  def WriteIfAt (x : &Nat) (y : &Nat) (e : Id Unit (AddM(y, 0)) ()) :
      Id Unit (WriteIf(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)) (*x := 7) :=
    WriteIfId(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)
  reject def WriteIfAtLie (x : &Nat) (y : &Nat) (e : Id Unit (AddM(y, 0)) ()) :
      Id Unit (WriteIf(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)) (*x := 8) :=
    WriteIfId(x, Id Unit (AddM(y, 0)) (), Eq Nat (*y) (*y), ⟨e, refl⟩)
  def TwoAt (y : &Nat) : Eq Nat (Two(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)) 2 :=
    TwoIs(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)
  reject def TwoAtLie (y : &Nat) : Eq Nat (Two(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)) 3 :=
    TwoIs(Id Unit (AddM(y, 0)) (), ⊤, ⟨AddMZero(y), refl⟩)
  -- a match on a proof outside tail position, then used
  def Snd (x : &Nat) (h : Eq Nat (*x) 0 ∧ Id Unit (AddM(x, 0)) ()) : Id Unit (AddM(x, 0)) () :=
    let k = match h { Intro(a, b) => b }; k
  -- matching on a proof does not move or inspect it: it is still usable afterwards
  def Twice (P : Prop) (Q : Prop) (h : P ∧ Q) : P ∧ P := let a = Fst(P, Q, h); match h { Intro(u, v) => ⟨a, u⟩ }
  -- Id over two owners computes to the library's And, which a match takes apart
  def SplitId (x : &Nat) (y : &Nat) (h : Id Unit (*x := 1; *y := 2) (*x := 3; *y := 4)) : Eq Nat 1 3 :=
    match h { Intro(a, b) => a }
  -- finding: And(True, P) ≡ P is normalisation, so h's type is P and there is no And to match
  reject def AndTrue (P : Prop) (h : ⊤ ∧ P) : P := match h { Intro(a, b) => b }
}

#eval IO.println (run "ByType" ByType).show

-- every verdict as expected, and exactly 19 assertions (a truncated file changes the count)
#guard (run "ByType" ByType).allAsExpected
#guard (run "ByType" ByType).count == 19

ochr OrAttack {
  inductive Bool := ff | tt
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
  -- elimination into propositions: every arm is a proof, so the match is one (⋆)
  def OrComm (P : Prop) (Q : Prop) (h : Or(P, Q)) : Or(Q, P) := match h { Inl(p) => Inr(p) | Inr(q) => Inl(q) }
  def OrElim (P : Prop) (Q : Prop) (R : Prop) (h : Or(P, Q)) (f : Π(p : P). R) (g : Π(q : Q). R) : R :=
    match h { Inl(p) => f(p) | Inr(q) => g(q) }
  def OrLet (P : Prop) (h : Or(P, P)) : P := let k : P = match h { Inl(p) => p | Inr(q) => q }; k
  -- large elimination would tell Inl from Inr, which proof irrelevance identifies: with
  -- IsL, Irr holds at the generic call (h = k = ⋆), and Irr(Inl(refl), Inr(refl)) would
  -- be Eq Bool tt ff, which is False (D47). D45 rejects IsL.
  reject def IsL (h : Or(True, True)) : Bool := match h { Inl(p) => tt | Inr(q) => ff }
  reject def Irr (h : Or(True, True)) (k : Or(True, True)) : Eq Bool (IsL(h)) (IsL(k)) := refl
  reject def Boom : False := Irr(Inl(refl), Inr(refl))
  -- without D45 but with D42 the machine cannot see Inl or Inr (a proof is ⋆), so no
  -- closed False follows; but it proves OrLie, whose model reading (IsL defined by its
  -- two cases) is Eq Bool tt ff: IsL has no model once proofs are irrelevant
  reject def OrLie : Eq Bool (IsL(Inl(refl))) (IsL(Inr(refl))) := refl
  -- one constructor with a data field is not a subsingleton either (the field is ⋆)
  inductive Sq : Prop := Mk(n : Nat)
  reject def Get (h : Sq) : Nat := match h { Mk(n) => n }
  reject def SqIrr (h : Sq) (k : Sq) : Eq Nat (Get(h)) (Get(k)) := refl
  reject def SqBoom : False := SqIrr(Mk(0), Mk(1))
  -- elimination of Sq into propositions is fine
  def SqTrue (h : Sq) : True := match h { Mk(n) => refl }
  -- a match that cannot pick an arm is a proof, erased wherever it runs (P2): EffL's calls
  -- run its body, which is such a match, so they write nothing. (Its typed check runs each
  -- arm's write in tail position, D41's tail-position gap: notes/lean-checker.md §12, §13.)
  def U (n : Nat) : Type := match n { Z => Prop | S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤ | S _ => ⊤ }
  def EffL (x : &Nat) (h : Or(⊤, ⊤)) : V(Z) := match h { Inl(p) => (*x := 1; refl) | Inr(q) => (*x := 2; refl) }
  def EffLNoop (x : &Nat) (h : Or(⊤, ⊤)) : Id Unit (let t = EffL(x, h); ()) () := refl
  reject def EffLOne (x : &Nat) (h : Or(⊤, ⊤)) : Id Unit (let t = EffL(x, h); ()) (*x := 1) := refl
  -- inline, outside tail position, the arms are erased occurrences and D41 rejects the writes
  reject def EffInline (x : &Nat) (h : Or(⊤, ⊤)) : Nat := let t : V(Z) = match h { Inl(p) => (*x := 1; refl) | Inr(q) => (*x := 2; refl) }; 0
}

#eval IO.println (run "OrAttack" OrAttack).show

-- every verdict as expected, and exactly 20 assertions (a truncated file changes the count)
#guard (run "OrAttack" OrAttack).allAsExpected
#guard (run "OrAttack" OrAttack).count == 20

ochr PList {
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  -- in-place append on a polymorphic list, and appending Nil has no effect, by bare
  -- recursion (the parameters of Nil come from AppendM's parameter type)
  def AppendM (A : Type) (xs : &List(A)) (ys : List(A)) : Unit by xs :=
    match *xs { Nil => *xs := ys | Cons(h, t) => AppendM(A, &t, ys) }
  def AppendMNil (A : Type) (xs : &List(A)) : Id Unit (AppendM(A, xs, Nil)) () by xs :=
    match *xs { Nil => refl | Cons(h, t) => AppendMNil(A, &t) }
  reject def AppendMOne (A : Type) (a : A) (xs : &List(A)) : Id Unit (AppendM(A, xs, Cons(a, Nil))) () by xs :=
    match *xs { Nil => refl | Cons(h, t) => AppendMOne(A, a, &t) }
  -- the pure append and its theorem, by the in-place lemma (as AddZero' from AddMZero)
  def Append (A : Type) (xs : List(A)) (ys : List(A)) : List(A) := AppendM(A, &xs, ys); xs
  def AppendNil (A : Type) (xs : List(A)) : Id (List(A)) (Append(A, xs, Nil)) xs := AppendMNil(A, &xs)
  -- instances: a list of lists, and a wrong statement (disjoint by D47)
  def AppendNilL (xs : List(List(Nat))) : Id (List(List(Nat))) (Append(List(Nat), xs, Nil)) xs := AppendNil(List(Nat), xs)
  def Closed : Id (List(Nat)) (Append(Nat, Cons(1, Nil), Nil)) (Cons(1, Nil)) := AppendNil(Nat, Cons(1, Nil))
  reject def ClosedWrong : Id (List(Nat)) (Append(Nat, Cons(1, Nil), Nil)) Nil := AppendNil(Nat, Cons(1, Nil))
  -- parameters: inferred from the fields, else from the required type, else an error
  def Ann : List(Nat) := let xs : List(Nat) = Nil; Cons(2, xs)
  reject def NoParam : Nat := let xs = Nil; 0
  reject def WrongParam : List(Nat) := Cons((), Nil)
  reject def Arity : List := Nil
  -- no borrows inside data, through a parameter either
  reject def BorrowList (x : &Nat) : Nat := let l : List(&Nat) = Nil; 0
  reject def BorrowCons (x : &Nat) : Nat := let l = Cons(x, (Nil : List(Nat))); 0
}

#eval IO.println (run "PList" PList).show

-- every verdict as expected, and exactly 15 assertions (a truncated file changes the count)
#guard (run "PList" PList).allAsExpected
#guard (run "PList" PList).count == 15

ochr PosParam {
  inductive Void : Type
  inductive Box (A : Type) := MkBox(x : A)
  def unbox (A : Type) (b : Box(A)) : A := match b { MkBox(x) => x }
  def absurdV (v : Void) : False := match v {}
  -- D36 with parameters: a negative occurrence hidden in a parameter instantiation is
  -- still rejected (a field's parameter arguments must be first-order too); without
  -- D36 the rest is a closed proof of False, typed by [Call-type] alone
  reject inductive Bad := Mk(f : Box(Π(x : Bad). Void))
  reject def L (b : Bad) : Void := match b { Mk(f) => match f { MkBox(g) => g(b) } }
  reject def K (b : Bad) : False := absurdV(L(b))
  reject def bad : Bad := Mk(MkBox(λ(x : Bad) : Void => L(x)))
  reject def Boom : False := K(bad)
  reject inductive Neg (A : Type) := MkNeg(f : Π(x : A). Nat)
  -- positive uses of parameters: nested (a list of the type itself), and proof fields
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  inductive Rose (A : Type) := Node(v : A, kids : List(Rose(A)))
  inductive Sig (P : Prop) := MkSig(n : Nat, h : P)
  def SigProof (P : Prop) (s : Sig(P)) : P := match s { MkSig(n, h) => h }
  def SigAt : Eq Nat 1 1 := SigProof(Eq Nat 1 1, MkSig(3, refl))
  -- universes are not cumulative: a proposition is not a Type parameter
  reject def PropBox : Type := Box(Eq Nat 0 1)
}

#eval IO.println (run "PosParam" PosParam).show

-- every verdict as expected, and exactly 16 assertions (a truncated file changes the count)
#guard (run "PosParam" PosParam).allAsExpected
#guard (run "PosParam" PosParam).count == 16

ochr Scrut {
  -- a match is on a place of its constructors' type, read from the place's type. v1.9's
  -- checker assumed it from the arms: it split the T(n)-typed x with L's constructors and
  -- accepted f and g, and at run time g(5) runs L's arms on the number 5
  inductive L := LNil | LCons(h : Nat, t : L)
  def T (n : Nat) : Type := match n { Z => L | S _ => Nat }
  reject def f (n : Nat) (x : T(n)) : Nat := match x { LNil => 0 | LCons(h, t) => 0 }
  reject def g (x : Nat) : Nat := f(1, x)
  def f0 (x : T(0)) : Nat := match x { LNil => 0 | LCons(h, t) => h }
  -- constructors are resolved by name, so a name is declared once
  inductive A := Mk(x : Nat)
  reject inductive B := Mk(y : Unit)
}

#eval IO.println (run "Scrut" Scrut).show

-- every verdict as expected, and exactly 7 assertions (a truncated file changes the count)
#guard (run "Scrut" Scrut).allAsExpected
#guard (run "Scrut" Scrut).count == 7

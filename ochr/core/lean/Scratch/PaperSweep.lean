import Ochr.Examples.«17HashMap»
import Ochr.Examples.«16Arrays»
open Ochr Ochr.Test
ochr SweepS2 {
  -- intro.typ:5
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y, S p => AddM(&p, y) }
  -- intro.typ:12
  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x := match *x { Z => refl, S p => AddMZero(&p) }
  -- overview.typ:27
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  -- overview.typ:94
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x, S p => TailM(&p) }
  -- overview.typ:94
  def AddM' (x : &Nat) (y : Nat) : Unit := let t = TailM(x); *t := y
  -- overview.typ:111
  def AddMEq (x : &Nat) (y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) by x := match *x { Z => refl, S p => AddMEq(&p, y) }
  -- overview.typ:122
  def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => True, S a' => match b { Z => False, S b' => Le(a', b') } }
  -- overview.typ:122
  def SubM (x : &Nat) (y : Nat) (h : Le(y, *x)) : Unit by y := match y { Z => (), S q => match *x { Z => match h {}, S p => *x := p; SubM(x, q, h) } }
  -- overview.typ:134
  def LeAdd (n : Nat) (m : Nat) : Le(n, Add(n, m)) by n := match n { Z => refl, S n' => LeAdd(n', m) }
  -- overview.typ:134
  def AddSub (x : &Nat) (y : Nat) : Unit := let old = clone(*x); AddM(&*x, y); SubM(x, old, LeAdd(old, y))
}
#eval IO.println (run "SweepS2" SweepS2).show
ochr SweepTrees uses Std {
  -- not printed: the tree, `Lt`, `Size`, `AddMS`/`AddS` as in InPlaceTrees
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)
  def Lt (a : Word) (b : Word) : Bool by a := match a { Zero => match b { Zero => false, Succ _ => true }, Succ a' => match b { Zero => false, Succ b' => Lt(a', b') } }
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := match *x { Z => refl, S p => AddMS(&p, y) }
  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)
  def Size (t : Tree) : Nat by t := match t { Leaf => 0, Node(l, v, r) => S (Add(Size(l), Size(r))) }
  -- overview.typ:146
  def InsertM (t : &Tree) (k : Word) : Unit by t := match *t { Leaf => *t := Node(Leaf, k, Leaf), Node(l, v, r) => let b = Lt(k, v); match b { true => InsertM(&l, k), false => InsertM(&r, k) } }
  -- overview.typ:146
  def Insert (t : Tree) (k : Word) : Tree := InsertM(&t, k); t
  -- overview.typ:156
  def SizeInsert (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t := match t { Leaf => refl, Node(l, v, r) => let b = Lt(k, v); match b { true => rewrite SizeInsert(l, k) in refl, false => rewrite SizeInsert(r, k) in rewrite AddS(Size(l), Size(r)) in refl } }
}
#eval IO.println (run "SweepTrees" SweepTrees).show
ochr SweepClear uses Std {
  -- overview.typ:170
  reject def Clear (x : &Nat) : Id Unit (match *x { Z => (), S p => p := Z }) () := refl
}
#eval IO.println (run "SweepClear" SweepClear).show
ochr SweepHM uses Std, HashMap, HashMapLookup {
  -- impl.typ:56
  def InsertFindOtherP (hm : &HashMap) (k : Word) (v : Nat) (k2 : Word) (h : Eq Bool (EqB(k, k2)) false) : Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2)) (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) := match *hm { HM(n, len, slots) => split BInsert in SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h) }
}
#eval IO.println (run "SweepHM" SweepHM).show
ochr SweepQS uses Quicksort {
  -- impl.typ:77
  def QSCorrectP (n : Word) (s : &Slice(Word, n)) (q : Word) : (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧ (let old = *s; Eq Word (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) := ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
}
#eval IO.println (run "SweepQS" SweepQS).show
ochr SweepApp1 {
  -- appendix.typ:547
  def U (n : Nat) : Type := match n { Z => Prop, S _ => Prop }
  -- appendix.typ:547
  def V (n : Nat) : U(n) := match n { Z => ⊤, S _ => ⊤ }
  -- appendix.typ:547
  def LieL (n : Nat) : Id Nat (let h = (λ(x : &Nat) : U(n) => (*x := S Z; V(n))); let c = Z; h(&c); c) (S Z) := refl
  -- appendix.typ:547
  reject def BoomL : Eq Nat Z (S Z) := LieL(Z)
  -- appendix.typ:555
  reject def LieB (n : Nat) : Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤), S _ => (c := S Z; ⊤) }; c) Z := refl
  -- appendix.typ:555
  reject def BoomB : Eq Nat (S Z) Z := LieB(Z)
  -- appendix.typ:561
  reject def LieH (g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let h = g(0); (c := S Z; h); c) (S Z) := refl
  -- appendix.typ:561
  reject def BoomH : Eq Nat Z (S Z) := LieH((λ(y : Nat) : V(Z) => refl))
  -- appendix.typ:567
  reject inductive Bad : Type := MkBad(f : Π(x : Bad). False)
  -- appendix.typ:567
  reject def L (b : Bad) : False := match b { MkBad(f) => f(b) }
  -- appendix.typ:567
  reject def Bad4 : False := L(MkBad(λ(x : Bad) : False => L(x)))
  -- appendix.typ:574
  inductive Box := MkBox(x : Nat)
  -- appendix.typ:574
  def Double (n : Nat) : Nat by n := match n { Z => Z, S p => S (S (Double(p))) }
  -- appendix.typ:574
  reject def Esc (n : Nat) (m : Box) : Id Nat (let b = Double(n); match b { Z => 0, S _ => 1 }) (match m { MkBox(x) => match x { Z => 0, S _ => 1 } }) := match m { MkBox(x) => match x { Z => refl, S _ => refl } }
  -- appendix.typ:574
  reject def Bad5 : Eq Nat 1 0 := Esc(1, MkBox(0))
  -- appendix.typ:595
  reject def Impred : Type := Π(x : &Type) (a : *x). *x
  -- appendix.typ:595
  reject def PolyId (x : &Type) (a : *x) : *x := a
  -- appendix.typ:595
  reject def SelfApp (u : Unit) : Impred := let T = Impred; PolyId(&T, PolyId)
}
#eval IO.println (run "SweepApp1" SweepApp1).show
ochr SweepApp2 uses Std {
  -- appendix.typ:587
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
  -- appendix.typ:587
  reject def IsL (h : Or(True, True)) : Bool := match h { Inl(p) => true, Inr(q) => false }
  -- appendix.typ:587
  reject def Irr (h : Or(True, True)) (k : Or(True, True)) : Eq Bool (IsL(h)) (IsL(k)) := refl
  -- appendix.typ:587
  reject def Boom : False := Irr(Inl(refl), Inr(refl))
}
#eval IO.println (run "SweepApp2" SweepApp2).show
-- inline fragments, verbatim inside the smallest program that runs them
ochr SweepInline uses Std, Fixtures {
  -- meta.typ:70 (naturality), at an abstract `n` and at 0, 1
  reject def PickEarly (n : Nat) (a : Nat) (b : Nat) : Unit := let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly0 (a : Nat) (b : Nat) : Unit := let n = 0; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly1 (a : Nat) (b : Nat) : Unit := let n = 1; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  -- eval.typ §4.3 closure fragments
  def CapCopy (x : &Nat) : Nat := let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)
  def TwiceMZeroFrag (x : &Nat) : Unit := let g = (λ(z : &Nat) : Unit => AddM(z, 0)); g(x)
  -- appendix note 27
  def CapS (x : &Nat) : Nat := AddM(&*x, 1); let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)
  -- typing.typ intro, obs.typ §5
  def LetZ (x : Nat) : Nat := let z = (let y = &x; *y := 2; x); let h : Id Nat z 2 = refl; z
  def WriteNeq (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Nat := match e {}
  reject def OwnedLocal (x : Nat) : Id Unit (x := 6) () := refl
  -- appendix notes 6, 7, 11, [Close]'s row
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y
  def PF (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e
  reject def QF (g : Π(n : Nat). &Nat) : False := PF(g(5), refl)
  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }
  reject def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()
}
#eval IO.println (run "SweepInline" SweepInline).show
-- appendix note 11's `G`, with `&` read from the declared type switched off
ochr SweepG uses Std {
  def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }
  def G (n : Nat) (a : Nat) : Unit := let r = F(n, &a); let b = a; let r2 = r; ()
  reject def UseG : Unit := G(0, 5)
}
#eval IO.println (run "SweepG" SweepG { refTop := false }).show


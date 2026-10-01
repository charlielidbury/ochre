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
  def AddSub (x : &Nat) (y : Nat) : Unit := let old = clone(*x); AddM(&*x, clone(y)); SubM(x, clone(old), LeAdd(old, y))
}
#eval IO.println (run "SweepS2" SweepS2).show
ochr SweepTrees uses Std {
  -- not printed: the tree, `Lt`, `Size`, `AddMS`/`AddS` as in InPlaceTrees
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)
  def Lt (a : Word) (b : Word) : Bool by a := match a { Zero => match b { Zero => false, Succ _ => true }, Succ a' => match b { Zero => false, Succ b' => Lt(a', b') } }
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := match *x { Z => refl, S p => AddMS(&p, y) }
  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)
  def Size (t : Tree) : Nat by t := match t { Leaf => 0, Node(l, v, r) => S (Add(Size(l), Size(r))) }
  -- overview.typ:147
  def InsertM (t : &Tree) (k : Word) : Unit by t := match *t { Leaf => *t := Node(Leaf, k, Leaf), Node(l, v, r) => let b = Lt(k, v); match b { true => InsertM(&l, k), false => InsertM(&r, k) } }
  -- overview.typ:147
  def Insert (t : Tree) (k : Word) : Tree := InsertM(&t, k); t
  -- overview.typ:157
  def SizeInsert (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t := match t { Leaf => refl, Node(l, v, r) => let b = Lt(k, v); match b { true => rewrite SizeInsert(l, k) in refl, false => rewrite SizeInsert(r, k) in rewrite AddS(Size(l), Size(r)) in refl } }
}
#eval IO.println (run "SweepTrees" SweepTrees).show
ochr SweepClear uses Std {
  -- overview.typ:171
  reject def Clear (x : &Nat) : Id Unit (match *x { Z => (), S p => p := Z }) () := refl
}
#eval IO.println (run "SweepClear" SweepClear).show
ochr SweepHM uses Std, HashMap, HashMapLookup {
  -- impl.typ:55
  def InsertFindOtherP (hm : &HashMap) (k : Word) (v : Nat) (k2 : Word) (h : Eq Bool (EqB(k, k2)) false) : Id Opt (InsertNoResize(&*hm, k, v); Find(clone(*hm), k2)) (let r = Find(clone(*hm), k2); InsertNoResize(&*hm, k, v); r) := match *hm { HM(n, len, slots) => split BInsert in SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h) }
}
#eval IO.println (run "SweepHM" SweepHM).show
ochr SweepQS uses Quicksort {
  -- impl.typ:76
  def QSCorrectP (n : Word) (s : &Slice(Word, n)) (q : Word) : (let c = *s; QS(n, n, &c); Sorted(n, c)) ∧ (let old = clone(*s); Eq Word (Count(q, n, (QS(n, n, &*s); *s))) (Count(q, n, old))) := ⟨QSSortedFull(n, n, s, LeRefl(n)), QSPerm(n, n, s, q)⟩
}
#eval IO.println (run "SweepQS" SweepQS).show
ochr SweepApp1 {
  -- appendix.typ:557
  def U (n : Nat) : Type₁ := match n { Z => Prop, S _ => Prop }
  -- appendix.typ:557
  def V (n : Nat) : U(n) := match n { Z => ⊤, S _ => ⊤ }
  -- appendix.typ:557
  def LieL (n : Nat) : Id Nat (let h = (λ(x : &Nat) : U(n) => (*x := S Z; V(n))); let c = Z; h(&c); c) (S Z) := refl
  -- appendix.typ:557
  reject def BoomL : Eq Nat Z (S Z) := LieL(Z)
  -- appendix.typ:565
  reject def LieB (n : Nat) : Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤), S _ => (c := S Z; ⊤) }; c) Z := refl
  -- appendix.typ:565
  reject def BoomB : Eq Nat (S Z) Z := LieB(Z)
  -- appendix.typ:571
  reject def LieH (g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let h = g(0); (c := S Z; h); c) (S Z) := refl
  -- appendix.typ:571
  reject def BoomH : Eq Nat Z (S Z) := LieH((λ(y : Nat) : V(Z) => refl))
  -- appendix.typ:577
  reject inductive Bad : Type := MkBad(f : Π(x : Bad). False)
  -- appendix.typ:577
  reject def L (b : Bad) : False := match b { MkBad(f) => f(b) }
  -- appendix.typ:577
  reject def Bad4 : False := L(MkBad(λ(x : Bad) : False => L(x)))
  -- appendix.typ:584
  inductive Box := MkBox(x : Nat)
  -- appendix.typ:584
  def Double (n : Nat) : Nat by n := match n { Z => Z, S p => S (S (Double(p))) }
  -- appendix.typ:584
  reject def Esc (n : Nat) (m : Box) : Id Nat (let b = Double(n); match b { Z => 0, S _ => 1 }) (match m { MkBox(x) => match x { Z => 0, S _ => 1 } }) := match m { MkBox(x) => match x { Z => refl, S _ => refl } }
  -- appendix.typ:584
  reject def Bad5 : Eq Nat 1 0 := Esc(1, MkBox(0))
  -- appendix.typ:605
  reject def Impred : Type := Π(x : &Type) (a : *x). *x
  -- appendix.typ:605
  reject def PolyId (x : &Type) (a : *x) : *x := a
  -- appendix.typ:605
  reject def SelfApp (u : Unit) : Impred := let T = Impred; PolyId(&T, PolyId)
}
#eval IO.println (run "SweepApp1" SweepApp1).show
ochr SweepApp2 uses Std {
  -- appendix.typ:597
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
  -- appendix.typ:597
  reject def IsL (h : Or(True, True)) : Bool := match h { Inl(p) => true, Inr(q) => false }
  -- appendix.typ:597
  reject def Irr (h : Or(True, True)) (k : Or(True, True)) : Eq Bool (IsL(h)) (IsL(k)) := refl
  -- appendix.typ:597
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
  -- D66: `&A` for `A : Type₀` is well formed; a type variable in `Type₁` is not
  def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()
  reject def SwapT1 (A : Type₁) (x : &A) (y : &A) : Unit := ()
}
#eval IO.println (run "SweepInline" SweepInline).show
-- dependent fields (appendix, impl §8.3): the growable vector and the arm assigning its two
-- fields in either order
ochr SweepDep uses ArrayBench {
  inductive Vec (E : Type) := MkVec(n : Word, items : Array(E, n))
  def Two : Array(Word, W(2)) := [Zero, Succ(Zero)]
  def SetTwo (v : &Vec(Word)) : Unit := match *v { MkVec(n, items) => (n := W(2); items := Two) }
  def SetTwoRev (v : &Vec(Word)) : Unit := match *v { MkVec(n, items) => (items := Two; n := W(2)) }
}
-- appendix A.4.8, nesting: `NBox` is accepted, `Bad` nested in it is not, and a field that is
-- a Π at the generic fields is rejected already
ochr SweepNest uses Std {
  inductive Void : Type
  def IsSucc (n : Word) : Prop := match n { Zero => False, Succ(_) => True }
  def NegIf (n : Word) (A : Type) : Type := match n { Zero => Unit, Succ(m) => Π(x : A). Void }
  inductive NBox (A : Type) := MkNBox(n : Word, f : NegIf(n, A), h : IsSucc(n))
  reject inductive Bad := MkBad(b : NBox(Bad))
  def Neg (A : Type) : Type := Π(x : A). Void
  reject inductive NegBox (A : Type) := MkNegBox(f : Neg(A))
}
#eval IO.println (run "SweepNest" SweepNest).show
#guard ((run "SweepNest" SweepNest { k4Nest := false }).rows.map (fun r => r.verdict matches .accepted)) == [true, true, true, true, true, true, false]
#eval IO.println (run "SweepDep" SweepDep).show
-- the typed-fragment appendix (tf.typ): Bad2 as printed and the claims around it. Since D67
-- (overwriting a borrow keeps the reborrows behind it) an assignment's [Access] leaves a
-- reborrow behind the old borrow alone, so the reborrow-and-replace idiom (Trav) and the
-- Pick variants are accepted on both paths
ochr SweepTF uses Std, Fixtures {
  def Bad2 (n : Nat) (b : Nat) (x : &Nat) : Unit := let a = 0; x := Pick(n, &a, &b); let z = b; ()
  def Bad2Run : Unit := (let y = 7; Bad2(0, 5, &y))
  def Bad4 (x : &Nat) (a : Nat) : Unit := (x := TailM(&a); match a { Z => (), S _ => () })
  def Bad4Run : Unit := (let c = 0; Bad4(&c, 1))
  reject def RetLocal (x : &Nat) : &Nat := (let a = 0; &a)
  reject def IdLet (a : Nat) : Id Nat (let z = a; a) a := refl
  reject def LetCode (a : Nat) : Nat := let z = a; a
  def AssignPick (n : Nat) (b : Nat) (x : &Nat) : Unit := (x := Pick(n, &*x, &b); *x := 5)
  def AssignPick1 (b : Nat) (c : Nat) : Unit := (let x = &c; let n = 1; x := Pick(n, &*x, &b); *x := 5)
  def AssignPickDrop (n : Nat) (b : Nat) (x : &Nat) : Unit := (x := Pick(n, &*x, &b); ())
  def ReborrowPick (n : Nat) (a : Nat) (b : Nat) (c : Nat) : Unit := (let x = Pick(n, &a, &b); let y = &*x; x := &c; *y := 0)
  def ReborrowPick0 (a : Nat) (b : Nat) (c : Nat) : Unit := (let n = 0; let x = Pick(n, &a, &b); let y = &*x; x := &c; *y := 0)
  def Trav (x : &Nat) : Unit := match *x { Z => (), S p => (x := &p; *x := 0) }
}
#eval IO.println (run "SweepTF" SweepTF).show
-- appendix note 11's `G`. The ochr command checks under the default configuration, where
-- `F` is rejected ([D48]); the note's point is with `&` read from the declared type switched
-- off (`refTop`), where `F` and `G` are accepted and `UseG` is not
ochr SweepG uses Std {
  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }
  reject def G (n : Nat) (a : Nat) : Unit := let r = F(n, &a); let b = a; let r2 = r; ()
  reject def UseG : Unit := G(0, 5)
}
#eval IO.println (run "SweepG" SweepG).show
#guard ((run "SweepG" SweepG { refTop := false }).rows.map (fun r => r.verdict matches .accepted)) == [true, true, false]


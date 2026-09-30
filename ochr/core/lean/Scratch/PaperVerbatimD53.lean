import Ochr.Examples.«17HashMap»
open Ochr Ochr.Test
/-! The paper's printed programs, run verbatim under moves (D53, the default since 20b8a80e),
against the paper at ochr-core 305f1c77. The paper's compact syntax is transliterated only as
far as the checker's surface needs (`def`, curried binders, `Type₀` → `Type`, a `λ` bound by
`let` parenthesised). `…Printed` is the text as printed; `…New` is the text proposed for the
paper, which is also the suite's (CurrentState.AddSub/AddSubStale, InPlaceTrees,
Snapshots.CapCopy/CapS, Naturality.PickEarly*, BorrowTypes.G/UseG,
HashMapLookup.InsertFindOther). Every other printed program is unchanged and still gets its
printed verdict. The arrays and quicksort blocks (QSCorrect, B1Join) were checked without D53
when this was written; since e4bb5d85 they check with it (`Test.preD53` is empty, and QSCorrect's
numbers are `Word`s), and `Scratch/paper_sweep.py` covers them. -/

-- §1–§2. Unchanged: AddM … AddToOne. Changed: AddSub (`*x` is moved out, so `&*x` borrows ⊥;
-- the printed AddSubStale is rejected for that reason, not because the requirement mentions
-- `Z`), and the §4.3 / note 27 closure fragments (a `Nat` read through a borrow moves, and a
-- closure body may not move what it captured).
ochr PaperMovesS2 {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y, S p => AddM(&p, y) }
  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
    match *x { Z => refl, S p => AddMZero(&p) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  def Add23 : Id Nat (Add(2, 3)) 5 := refl
  def AddZero (x : Nat) : Id Nat (Add(x, 0)) x := AddMZero(&x)
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x, S p => TailM(&p) }
  def AddM' (x : &Nat) (y : Nat) : Unit := let t = TailM(x); *t := y
  def AddMEq (x : &Nat) (y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) by x :=
    match *x { Z => refl, S p => AddMEq(&p, y) }
  def Le (a : Nat) (b : Nat) : Prop by a :=
    match a { Z => True, S a' => match b { Z => False, S b' => Le(a', b') } }
  def SubM (x : &Nat) (y : Nat) (h : Le(y, *x)) : Unit by y :=
    match y { Z => (), S q => match *x { Z => match h {}, S p => *x := p; SubM(x, q, h) } }
  def LeAdd (n : Nat) (m : Nat) : Le(n, Add(n, m)) by n := match n { Z => refl, S n' => LeAdd(n', m) }
  reject def AddSubPrinted (x : &Nat) (y : Nat) : Unit := let old = *x; AddM(&*x, y); SubM(x, old, LeAdd(old, y))
  reject def AddSubStalePrinted (x : &Nat) (y : Nat) : Unit := let old = *x; AddM(&*x, y); *x := Z; SubM(x, old, LeAdd(old, y))
  def AddSubNew (x : &Nat) (y : Nat) : Unit := let old = clone(*x); AddM(&*x, y); SubM(x, old, LeAdd(old, y))
  reject def AddSubStaleNew (x : &Nat) (y : Nat) : Unit := let old = clone(*x); AddM(&*x, y); *x := Z; SubM(x, old, LeAdd(old, y))
  def AddToOne (b : Nat) (x₁ : &Nat) (x₂ : &Nat) (y : Nat) : Unit := let r = match b { Z => x₁, S _ => x₂ }; AddM(r, y)
  reject def CapCopyPrinted (x : &Nat) : Nat := let n = *x; let f = (λ(y : Nat) : Nat => n); f(0)
  reject def CapCopyLetOnly (x : &Nat) : Nat := let n = clone(*x); let f = (λ(y : Nat) : Nat => n); f(0)
  def CapCopyNew (x : &Nat) : Nat := let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)
  reject def CapSPrinted (x : &Nat) : Nat := AddM(&*x, 1); let n = *x; let f = (λ(y : Nat) : Nat => n); f(0)
  def CapSNew (x : &Nat) : Nat := AddM(&*x, 1); let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)
}
#guard (run "PaperMovesS2" PaperMovesS2).allAsExpected

-- §2 Trees, as printed (`k : Nat`, and a tree of `Nat`s): `Lt(k, v)` moves the key, and the
-- recursive call then reads it again.
ochr PaperMovesTreesNat uses Std {
  inductive Tree := Leaf | Node(l : Tree, v : Nat, r : Tree)
  def Lt (a : Nat) (b : Nat) : Bool by a := match a { Z => match b { Z => false, S _ => true }, S a' => match b { Z => false, S b' => Lt(a', b') } }
  reject def InsertM (t : &Tree) (k : Nat) : Unit by t :=
    match *t { Leaf          => *t := Node(Leaf, k, Leaf),
               Node(l, v, r) => let b = Lt(k, v);
                                match b { true => InsertM(&l, k), false => InsertM(&r, k) } }
  reject def Insert (t : Tree) (k : Nat) : Tree := InsertM(&t, k); t
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := match *x { Z => refl, S p => AddMS(&p, y) }
  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)
  def Size (t : Tree) : Nat by t := match t { Leaf => 0, Node(l, v, r) => S (Add(Size(l), Size(r))) }
  reject def SizeInsert (t : Tree) (k : Nat) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => rewrite SizeInsert(l, k) in refl,
                false => rewrite SizeInsert(r, k) in rewrite AddS(Size(l), Size(r)) in refl } }
}
#guard (run "PaperMovesTreesNat" PaperMovesTreesNat).allAsExpected

-- §2 Trees, new text: `Word` keys (a copy type), as InPlaceTrees.
ochr PaperMovesTreesWord uses Std {
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)
  def Lt (a : Word) (b : Word) : Bool by a := match a { Zero => match b { Zero => false, Succ _ => true }, Succ a' => match b { Zero => false, Succ b' => Lt(a', b') } }
  def InsertM (t : &Tree) (k : Word) : Unit by t :=
    match *t { Leaf          => *t := Node(Leaf, k, Leaf),
               Node(l, v, r) => let b = Lt(k, v);
                                match b { true => InsertM(&l, k), false => InsertM(&r, k) } }
  def Insert (t : Tree) (k : Word) : Tree := InsertM(&t, k); t
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := match *x { Z => refl, S p => AddMS(&p, y) }
  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)
  def Size (t : Tree) : Nat by t := match t { Leaf => 0, Node(l, v, r) => S (Add(Size(l), Size(r))) }
  def SizeInsert (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => rewrite SizeInsert(l, k) in refl,
                false => rewrite SizeInsert(r, k) in rewrite AddS(Size(l), Size(r)) in refl } }
}
#guard (run "PaperMovesTreesWord" PaperMovesTreesWord).allAsExpected

-- §7.3 naturality: `Pick(n, …)` moves `n`, so the printed program is rejected at every `n`
-- for matching on a moved value; with `clone(n)` it is rejected only at the abstract `n`, as
-- the text says, and runs at 0 and 1.
ochr PaperMovesMeta uses Fixtures {
  reject def PickEarlyPrinted (n : Nat) (a : Nat) (b : Nat) : Unit := let r = Pick(n, &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  reject def PickEarly0Printed (a : Nat) (b : Nat) : Unit := let n = 0; let r = Pick(n, &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  reject def PickEarlyNew (n : Nat) (a : Nat) (b : Nat) : Unit := let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly0New (a : Nat) (b : Nat) : Unit := let n = 0; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly1New (a : Nat) (b : Nat) : Unit := let n = 1; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
}
#guard (run "PaperMovesMeta" PaperMovesMeta).allAsExpected

-- Appendix note 11, with `&` read from the declared type switched off (`refTop`): the printed
-- `G` reads the moved `r` a second time and is rejected at the generic call already; the new
-- `G` is accepted there and reads `⊥` at `n = 0`, as BorrowTypes.G/UseG.
-- (Checked at elaboration under the default configuration, where `F` is rejected, so every
-- declaration is marked `reject`; the verdicts with `refTop` off are asserted below.)
ochr PaperMovesG uses Std {
  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }
  reject def GPrinted (n : Nat) (a : Nat) : Nat := let r = F(n, &a); let r2 = r; let r3 = r; a
  reject def GNew (n : Nat) (a : Nat) : Unit := let r = F(n, &a); let b = a; let r2 = r; ()
  reject def UseGNew : Unit := GNew(0, 5)
}
#guard ((run "PaperMovesG" PaperMovesG { refTop := false }).rows.map (fun r => r.verdict matches .accepted)) == [true, false, true, false]

-- §8.2: the keys are `Word`s.
ochr PaperMovesHM uses Std, HashMap, HashMapLookup {
  reject def InsertFindOtherPrinted (hm : &HashMap) (k : Nat) (v : Nat) (k2 : Nat)
                (h : Eq Bool (EqB(k, k2)) false) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2))
           (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) :=
  match *hm { HM(n, len, slots) =>
    split BInsert in SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h) }
  def InsertFindOtherNew (hm : &HashMap) (k : Word) (v : Nat) (k2 : Word)
                (h : Eq Bool (EqB(k, k2)) false) :
    Id Opt (InsertNoResize(&*hm, k, v); Find(*hm, k2))
           (let r = Find(*hm, k2); InsertNoResize(&*hm, k, v); r) :=
  match *hm { HM(n, len, slots) =>
    split BInsert in SlotInsertFindOther(&slots, Idx(k, n), Idx(k2, n), k, v, k2, h) }
}
#guard (run "PaperMovesHM" PaperMovesHM).allAsExpected

-- Unchanged under moves: §5, §6 and the appendix notes' programs, verbatim.
ochr PaperMovesUnchanged uses Std {
  def WriteNeq (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Nat := match e {}
  reject def OwnedLocal (x : Nat) : Id Unit (x := 6) () := refl
  def LetZ (x : Nat) : Nat := let z = (let y = &x; *y := 2; x); let h : Id Nat z 2 = refl; z
  reject def LamWrite : (Π(x : &Nat). Id Nat (*x) 5) := λ(x : &Nat) : Id Nat (*x) 5 => (*x := 5; refl)
  def U (n : Nat) : Type := match n { Z => Prop, S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤, S _ => ⊤ }
  def LieL (n : Nat) : Id Nat (let h = (λ(x : &Nat) : U(n) => (*x := S Z; V(n))); let c = Z; h(&c); c) (S Z) := refl
  reject def BoomL : Eq Nat Z (S Z) := LieL(Z)
  reject def LieB (n : Nat) : Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤), S _ => (c := S Z; ⊤) }; c) Z := refl
  reject def LieH (g : Π(y : Nat). V(Z)) : Id Nat (let c = Z; let h = g(0); (c := S Z; h); c) (S Z) := refl
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y
  def PF (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e
  reject def QF (g : Π(n : Nat). &Nat) : False := PF(g(5), refl)
  inductive Or (P : Prop) (Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)
  reject def IsL (h : Or(True, True)) : Bool := match h { Inl(p) => true, Inr(q) => false }
  reject def Impred : Type := Π(x : &Type) (a : *x). *x
  reject def PolyId (x : &Type) (a : *x) : *x := a
  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }
  reject def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()
}
#guard (run "PaperMovesUnchanged" PaperMovesUnchanged).allAsExpected

-- Notes 4 and 5 declare their own `Box` and `Bad`, so they do not use `Std`.
ochr PaperMovesNotes45 {
  reject inductive Bad : Type := MkBad(f : Π(x : Bad). False)
  inductive Box := MkBox(x : Nat)
  def Double (n : Nat) : Nat by n := match n { Z => Z, S p => S (S (Double(p))) }
  reject def Esc (n : Nat) (m : Box) : Id Nat (let b = Double(n); match b { Z => 0, S _ => 1 }) (match m { MkBox(x) => match x { Z => 0, S _ => 1 } }) :=
    match m { MkBox(x) => match x { Z => refl, S _ => refl } }
}
#guard (run "PaperMovesNotes45" PaperMovesNotes45).allAsExpected

#eval IO.println (run "PaperMovesS2" PaperMovesS2).show
#eval IO.println (run "PaperMovesTreesNat" PaperMovesTreesNat).show
#eval IO.println (run "PaperMovesMeta" PaperMovesMeta).show
#eval IO.println (run "PaperMovesG" PaperMovesG).show
#eval IO.println (run "PaperMovesHM" PaperMovesHM).show

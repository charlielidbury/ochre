import Ochr.Examples.V15

/-! # General inductive types: lists and binary search trees

reviewer-1: "every example is on Peano naturals, where each value has one sub-place".
These have several constructors and several fields: pattern variables are the field
places `p.f`, [Split] refines `σ` to `C(σ₁ … σₖ)`, and [Rec] measures strict subterms
across all fields. In `InsertM` a comparison decides which sub-tree is mutated. -/

open Ochr.Test

ochr Inductives {
  inductive List := Nil | Cons(h : Nat, t : List)

  -- (a) in-place append, and appending Nil has no effect, by bare recursion
  def AppendM (xs : &List) (ys : List) : Unit by xs :=
    match *xs { Nil => *xs := ys | Cons(h, t) => AppendM(&t, ys) }
  def AppendMNil (xs : &List) : Id Unit (AppendM(xs, Nil)) () by xs :=
    match *xs { Nil => refl | Cons(h, t) => AppendMNil(&t) }
  reject def AppendMOne (xs : &List) : Id Unit (AppendM(xs, Cons(0, Nil))) () by xs :=
    match *xs { Nil => refl | Cons(h, t) => AppendMOne(&t) }

  -- (b) the returned-borrow analogue: a borrow of the final Nil
  def LastM (xs : &List) : &List by xs :=
    match *xs { Nil => xs | Cons(h, t) => LastM(&t) }
  def AppendM' (xs : &List) (ys : List) : Unit := let r = LastM(xs); *r := ys
  def AppendMEq (xs : &List) (ys : List) : Id Unit (AppendM(xs, ys)) (AppendM'(xs, ys)) by xs :=
    match *xs { Nil => refl | Cons(h, t) => AppendMEq(&t, ys) }

  -- (c) binary search trees
  inductive Bool := false | true      -- (v2.0: `False`, `True` are the library propositions)
  inductive Tree := Leaf | Node(l : Tree, v : Nat, r : Tree)
  def Lt (a : Nat) (b : Nat) : Bool by a :=
    match a { Z => match b { Z => false | S _ => true } | S a' => match b { Z => false | S b' => Lt(a', b') } }

  -- in-place insert: the comparison decides which sub-place is mutated
  def InsertM (t : &Tree) (k : Nat) : Unit by t :=
    match *t {
      Leaf => *t := Node(Leaf, k, Leaf)
    | Node(l, v, r) => let b = Lt(k, v); match b { false => InsertM(&r, k) | true => InsertM(&l, k) } }
  -- the pure insert
  def Insert (t : Tree) (k : Nat) : Tree by t :=
    match t {
      Leaf => Node(Leaf, k, Leaf)
    | Node(l, v, r) => let b = Lt(k, v); match b { false => Node(l, v, Insert(r, k)) | true => Node(Insert(l, k), v, r) } }
  -- the in-place insert is the pure insert, by bare recursion (needs finding G1: the
  -- split on Lt(k, v) must reach the copies of that comparison inside the goal)
  def InsertMEq (t : &Tree) (k : Nat) : Id Unit (InsertM(t, k)) (*t := Insert(*t, k)) by t :=
    match *t {
      Leaf => refl
    | Node(l, v, r) => let b = Lt(k, v); match b { false => InsertMEq(&r, k) | true => InsertMEq(&l, k) } }
  -- an insert that goes the wrong way is not the pure insert
  def InsertMSwap (t : &Tree) (k : Nat) : Unit by t :=
    match *t {
      Leaf => *t := Node(Leaf, k, Leaf)
    | Node(l, v, r) => let b = Lt(k, v); match b { false => InsertMSwap(&l, k) | true => InsertMSwap(&r, k) } }
  reject def InsertMSwapEq (t : &Tree) (k : Nat) : Id Unit (InsertMSwap(t, k)) (*t := Insert(*t, k)) by t :=
    match *t {
      Leaf => refl
    | Node(l, v, r) => let b = Lt(k, v); match b { false => InsertMSwapEq(&l, k) | true => InsertMSwapEq(&r, k) } }
  -- recursing on the node itself, not a sub-tree
  reject def InsertLoop (t : &Tree) (k : Nat) : Unit by t :=
    match *t { Leaf => () | Node(l, v, r) => InsertLoop(t, k) }

  -- a measure: inserting grows the size by one. The true arm is definitional after the
  -- IH (Add recurses on its first argument); the false arm needs x + S y = S (x + y),
  -- itself proved in place by bare recursion. Both arms rewrite with J.
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x :=
    match *x { Z => refl | S p => AddMS(&p, y) }
  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)
  def Size (t : Tree) : Nat by t := match t { Leaf => 0 | Node(l, v, r) => S (Add(Size(l), Size(r))) }
  def SizeInsert (t : Tree) (k : Nat) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
    match t {
      Leaf => refl
    | Node(l, v, r) => let b = Lt(k, v); match b {
        false =>
          J(Nat, Add(Size(l), S (Size(r))), S (Add(Size(l), Size(r))),
            λ(z : Nat) : Prop => Id Nat (S z) (S (Add(Size(l), Size(Insert(r, k))))),
            AddS(Size(l), Size(r)),
            J(Nat, S (Size(r)), Size(Insert(r, k)),
              λ(z : Nat) : Prop => Id Nat (S (Add(Size(l), S (Size(r))))) (S (Add(Size(l), z))),
              SizeInsert(r, k), refl))
      | true =>
          J(Nat, S (Size(l)), Size(Insert(l, k)),
            λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(z, Size(r)))),
            SizeInsert(l, k), refl) } }
  -- without the arithmetic lemma the false arm does not check
  reject def SizeInsertNoLemma (t : Tree) (k : Nat) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
    match t {
      Leaf => refl
    | Node(l, v, r) => let b = Lt(k, v); match b {
        false =>
          J(Nat, S (Size(r)), Size(Insert(r, k)),
            λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(Size(l), z))),
            SizeInsertNoLemma(r, k), refl)
      | true =>
          J(Nat, S (Size(l)), Size(Insert(l, k)),
            λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(z, Size(r)))),
            SizeInsertNoLemma(l, k), refl) } }
  reject def SizeInsertTwo (t : Tree) (k : Nat) : Id Nat (S (S (Size(t)))) (Size(Insert(t, k))) by t :=
    match t { Leaf => refl | Node(l, v, r) => SizeInsertTwo(l, k) }
}

#eval IO.println (run "Inductives" Inductives).show

-- every verdict as expected, and exactly 24 assertions (a truncated file changes the count)
#guard (run "Inductives" Inductives).allAsExpected
#guard (run "Inductives" Inductives).count == 24

import Ochr.Examples.«00Std»

/-! # 10. Inductive types: lists, trees, and parameters

`inductive D (a : A) … := C₁(f : T, …) | …` declares a type with constructors. A match on a
value of `D` has one arm per constructor, and its pattern variables name the field places
`p.f`, as `S y` names `p.1`. [Split] refines an abstract value to `C(σ₁, …, σₖ)`, and [Rec]
accepts a recursive call on any field. Parameters are uniform (`List(A)`); a constructor
takes them first, written `Cons[Nat](1, Nil[Nat])` or left out when they can be inferred
(D46, D49). A field's type is first-order data: other inductive types, the type itself,
`Nat`, `Unit`, `×` or a parameter, but no function type and no borrow (strict positivity,
D36). Constructor names are unique in a program.

Defined in RULES §8. -/

open Ochr.Test

/-! ## Lists

In-place append and its theorems are the same bare recursion as `AddM`'s, and `LastM` is
the list version of `TailM`. -/

ochr Lists {
  inductive List := Nil | Cons(h : Nat, t : List)

  -- In-place append, and appending `Nil` does nothing.
  def AppendM (xs : &List) (ys : List) : Unit by xs := (
    match *xs {
      Nil => *xs := ys,
      Cons(h, t) => AppendM(&t, ys),
    }
  )

  def AppendMNil (xs : &List) : Id Unit (AppendM(xs, Nil)) () by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMNil(&t),
    }
  )

  -- Appending a one-element list does something.
  reject def AppendMOne (xs : &List) : Id Unit (AppendM(xs, Cons(0, Nil))) () by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMOne(&t),
    }
  )

  -- A borrow of the final `Nil`, and append by writing through it.
  def LastM (xs : &List) : &List by xs := (
    match *xs {
      Nil => xs,
      Cons(h, t) => LastM(&t),
    }
  )

  def AppendM' (xs : &List) (ys : List) : Unit := (
    let r = LastM(xs);
    *r := ys
  )

  def AppendMEq (xs : &List) (ys : List) : Id Unit (AppendM(xs, ys)) (AppendM'(xs, ys)) by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMEq(&t, ys),
    }
  )

  -- Constructors are resolved by name, so a name is declared once in a program.
  inductive A := Make(x : Nat)
  reject inductive B := Make(y : Unit)
}

#eval IO.println (run "Lists" Lists).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Lists" Lists).allAsExpected
#guard (run "Lists" Lists).count == 9

/-! ## Binary search trees

In `InsertM` a comparison decides which subtree is changed. The comparison `Lt(k, v)` is a
sealed program, so a match on it first replaces it by a fresh value (switch `generalize`).
That the in-place insert is the pure insert is then bare recursion, provided the
replacement also reaches the copies of the comparison that the goal computes later (D34,
switch `genConsistent`). The size theorem needs one arithmetic lemma, proved in place. -/

ochr Trees uses Std {
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)

  -- The order on keys: words, which every read copies (D53).
  def Lt (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => false,
        Succ _ => true,
      },
      Succ a' => match b {
        Zero => false,
        Succ b' => Lt(a', b'),
      },
    }
  )

  -- In-place insert.
  def InsertM (t : &Tree) (k : Word) : Unit by t := (
    match *t {
      Leaf => *t := Node(Leaf, k, Leaf),
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          true => InsertM(&l, k),
          false => InsertM(&r, k),
        }
      ),
    }
  )

  -- Pure insert.
  def Insert (t : Tree) (k : Word) : Tree by t := (
    match t {
      Leaf => Node(Leaf, k, Leaf),
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false => Node(l, v, Insert(r, k)),
          true => Node(Insert(l, k), v, r),
        }
      ),
    }
  )

  -- The in-place insert is the pure insert.
  def InsertMEq (t : &Tree) (k : Word) : Id Unit (InsertM(t, k)) (*t := Insert(*t, k)) by t := (
    match *t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          true => InsertMEq(&l, k),
          false => InsertMEq(&r, k),
        }
      ),
    }
  )

  -- An insert that goes the wrong way is not.
  def InsertMSwap (t : &Tree) (k : Word) : Unit by t := (
    match *t {
      Leaf => *t := Node(Leaf, k, Leaf),
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false => InsertMSwap(&l, k),
          true => InsertMSwap(&r, k),
        }
      ),
    }
  )

  reject def InsertMSwapEq (t : &Tree) (k : Word) : Id Unit (InsertMSwap(t, k)) (*t := Insert(*t, k)) by t := (
    match *t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false => InsertMSwapEq(&l, k),
          true => InsertMSwapEq(&r, k),
        }
      ),
    }
  )

  -- Recursing on the node itself, not on a subtree, is not structural.
  reject def InsertLoop (t : &Tree) (k : Word) : Unit by t := (
    match *t {
      Leaf => (),
      Node(l, v, r) => InsertLoop(t, k),
    }
  )

  -- Inserting grows the size by one. In the `true` arm this follows from the induction
  -- hypothesis, since `Add` recurses on its first argument. The `false` arm needs
  -- `x + S y = S (x + y)`, itself proved in place by bare recursion. Both arms rewrite
  -- with `J`.
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := (
    match *x {
      Z => refl,
      S p => AddMS(&p, y),
    }
  )

  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)

  def Size (t : Tree) : Nat by t := (
    match t {
      Leaf => 0,
      Node(l, v, r) => S (Add(Size(l), Size(r))),
    }
  )

  def SizeInsert (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false =>
            J(
              Nat,
              Add(Size(l), S (Size(r))),
              S (Add(Size(l), Size(r))),
              λ(z : Nat) : Prop => Id Nat (S z) (S (Add(Size(l), Size(Insert(r, k))))),
              AddS(Size(l), Size(r)),
              J(
                Nat,
                S (Size(r)),
                Size(Insert(r, k)),
                λ(z : Nat) : Prop => Id Nat (S (Add(Size(l), S (Size(r))))) (S (Add(Size(l), z))),
                SizeInsert(r, k),
                refl
              )
            ),
          true =>
            J(
              Nat,
              S (Size(l)),
              Size(Insert(l, k)),
              λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(z, Size(r)))),
              SizeInsert(l, k),
              refl
            ),
        }
      ),
    }
  )

  -- Without the arithmetic lemma the `false` arm does not check ...
  reject def SizeInsertNoLemma (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => (
        let b = Lt(k, v);
        match b {
          false =>
            J(
              Nat,
              S (Size(r)),
              Size(Insert(r, k)),
              λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(Size(l), z))),
              SizeInsertNoLemma(r, k),
              refl
            ),
          true =>
            J(
              Nat,
              S (Size(l)),
              Size(Insert(l, k)),
              λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(z, Size(r)))),
              SizeInsertNoLemma(l, k),
              refl
            ),
        }
      ),
    }
  )

  -- ... and inserting does not grow the size by two.
  reject def SizeInsertTwo (t : Tree) (k : Word) : Id Nat (S (S (Size(t)))) (Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => SizeInsertTwo(l, k),
    }
  )
}

#eval IO.println (run "Trees" Trees).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Trees" Trees).allAsExpected
#guard (run "Trees" Trees).count == 14

/-! ## The paper's trees: the pure insert runs the in-place one

The paper (§2, Trees) defines the pure insert as `Add` is defined, by running the in-place
one on a copy, and proves the size theorem about it. `InsertM`, `Insert` and `SizeInsert`
are the paper's text, in its layout, with `Word` keys (D53: a key is only compared, so it is a
copy); `Lt` and `Size` are the ones it assumes, and `AddS`
(`x + S y = S (x + y)`) is proved in place by bare recursion (`AddMS`) and transferred to
`Add` by lending, as the prose says. The in-place insert is the pure one by definition
(`InsertMIsInsert`, by `refl`). -/

ochr InPlaceTrees uses Std {
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)

  def Lt (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b { Zero => false, Succ _ => true },
      Succ a' => match b { Zero => false, Succ b' => Lt(a', b') },
    }
  )

  def InsertM (t : &Tree) (k : Word) : Unit by t :=
    match *t { Leaf          => *t := Node(Leaf, k, Leaf),
               Node(l, v, r) => let b = Lt(k, v);
                                match b { true => InsertM(&l, k), false => InsertM(&r, k) } }
  def Insert (t : Tree) (k : Word) : Tree := InsertM(&t, k); t

  def InsertMIsInsert (t : &Tree) (k : Word) : Id Unit (InsertM(t, k)) (*t := Insert(*t, k)) := refl

  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := (
    match *x {
      Z => refl,
      S p => AddMS(&p, y),
    }
  )

  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)

  def Size (t : Tree) : Nat by t := (
    match t {
      Leaf => 0,
      Node(l, v, r) => S (Add(Size(l), Size(r))),
    }
  )

  def SizeInsert (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => J(Nat, S (Size(l)), Size(Insert(l, k)),
                           λ(z : Nat) : Prop => Id Nat (S (S (Add(Size(l), Size(r))))) (S (Add(z, Size(r)))),
                           SizeInsert(l, k), refl),
                false => J(Nat, Add(Size(l), S (Size(r))), S (Add(Size(l), Size(r))),
                           λ(z : Nat) : Prop => Id Nat (S z) (S (Add(Size(l), Size(Insert(r, k))))),
                           AddS(Size(l), Size(r)),
                           J(Nat, S (Size(r)), Size(Insert(r, k)),
                             λ(z : Nat) : Prop => Id Nat (S (Add(Size(l), S (Size(r))))) (S (Add(Size(l), z))),
                             SizeInsert(r, k), refl)) } }

  -- The same theorem with D60's `rewrite` instead of `J`, in the paper's layout.
  def SizeInsertRw (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => rewrite SizeInsertRw(l, k) in refl,
                false => rewrite SizeInsertRw(r, k) in rewrite AddS(Size(l), Size(r)) in refl } }

  -- Without `AddS` the `false` arm does not check: rewriting with the induction hypothesis
  -- alone leaves `S (Add(Size(l), Size(r)))` against `Add(Size(l), S (Size(r)))`.
  reject def SizeInsertRwNoLemma (t : Tree) (k : Word) : Id Nat (S (Size(t))) (Size(Insert(t, k))) by t :=
    match t { Leaf => refl,
              Node(l, v, r) => let b = Lt(k, v); match b {
                true  => rewrite SizeInsertRwNoLemma(l, k) in refl,
                false => rewrite SizeInsertRwNoLemma(r, k) in refl } }

  -- Inserting does not grow the size by two.
  reject def SizeInsertTwo (t : Tree) (k : Word) : Id Nat (S (S (Size(t)))) (Size(Insert(t, k))) by t := (
    match t {
      Leaf => refl,
      Node(l, v, r) => SizeInsertTwo(l, k),
    }
  )
}

#eval IO.println (run "InPlaceTrees" InPlaceTrees).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "InPlaceTrees" InPlaceTrees).allAsExpected
#guard (run "InPlaceTrees" InPlaceTrees).count == 12

/-! ## Parameters: a polymorphic list

`List(A)` is `Std`'s. -/

ochr PolyLists uses Std {
  -- In-place append on `List(A)`, and appending `Nil` does nothing; `Nil`'s parameter comes
  -- from `AppendM`'s parameter type.
  def AppendM (A : Type) (xs : &List(A)) (ys : List(A)) : Unit by xs := (
    match *xs {
      Nil => *xs := ys,
      Cons(h, t) => AppendM(A, &t, ys),
    }
  )

  def AppendMNil (A : Type) (xs : &List(A)) : Id Unit (AppendM(A, xs, Nil)) () by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMNil(A, &t),
    }
  )

  reject def AppendMOne (A : Type) (a : A) (xs : &List(A)) :
      Id Unit (AppendM(A, xs, Cons(a, Nil))) () by xs := (
    match *xs {
      Nil => refl,
      Cons(h, t) => AppendMOne(A, a, &t),
    }
  )

  -- The pure append, and its theorem from the in-place lemma (as `AddZero'` from
  -- `AddMZero`).
  def Append (A : Type) (xs : List(A)) (ys : List(A)) : List(A) := (
    AppendM(A, &xs, ys);
    xs
  )

  def AppendNil (A : Type) (xs : List(A)) : Id (List(A)) (Append(A, xs, Nil)) xs := AppendMNil(A, &xs)

  -- Instances: a list of lists, a closed list, and a wrong statement (the two lists have
  -- different constructors, D47).
  def AppendNilL (xs : List(List(Nat))) : Id (List(List(Nat))) (Append(List(Nat), xs, Nil)) xs := (
    AppendNil(List(Nat), xs)
  )

  def Closed : Id (List(Nat)) (Append(Nat, Cons(1, Nil), Nil)) (Cons(1, Nil)) := AppendNil(Nat, Cons(1, Nil))
  reject def ClosedWrong : Id (List(Nat)) (Append(Nat, Cons(1, Nil), Nil)) Nil := AppendNil(Nat, Cons(1, Nil))

  -- Parameters written out ...
  def Explicit : List(Nat) := Cons[Nat](1, Nil[Nat])
  reject def ExplicitWrong : List(Nat) := Cons[Unit](1, Nil[Unit])
  def PairP (P : Prop) (Q : Prop) (h : P) (k : Q) : P ∧ Q := Intro[P, Q](h, k)

  -- ... or inferred: from the fields, else from the type the context requires, else it is
  -- an error.
  def Ann : List(Nat) := (
    let xs : List(Nat) = Nil;
    Cons(2, xs)
  )

  reject def NoParam : Nat := (
    let xs = Nil;
    0
  )

  reject def WrongParam : List(Nat) := Cons((), Nil)
  reject def Arity : List := Nil

  -- A constructor value records its parameters, so a closure that captures `Nil` can give
  -- it a type.
  def CapNil (u : Unit) : Nat := (
    let xs = Nil[Nat];
    let f = (λ(n : Nat) : List(Nat) => clone(xs));
    0
  )

  def CapNilAnn (u : Unit) : Nat := (
    let xs : List(Nat) = Nil;
    let f = (λ(n : Nat) : List(Nat) => clone(xs));
    0
  )

  -- No borrows inside data, through a parameter either.
  reject def BorrowList (x : &Nat) : Nat := (
    let l : List(&Nat) = Nil;
    0
  )

  reject def BorrowCons (x : &Nat) : Nat := (
    let l = Cons(x, (Nil : List(Nat)));
    0
  )
}

#eval IO.println (run "PolyLists" PolyLists).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "PolyLists" PolyLists).allAsExpected
#guard (run "PolyLists" PolyLists).count == 19

/-! ## What goes wrong without strict positivity

A field of function type can mention the type being declared negatively. Then `L(b)`
applies `b`'s own field to `b`, which never terminates, but `K` is typed by [Call-type]
alone and proofs are not run, so `Boom` is a closed proof of `False` (D36, switch
`positivity`). Fields of first-order data are fine. `Empty` is in `Fixtures`. -/

ochr Positivity uses Fixtures {
  def absurd (e : Empty) : False by e := (
    match e {
      E(e') => absurd(e'),
    }
  )

  reject inductive Bad := MkBad(f : Π(x : Bad). Empty)

  reject def L (b : Bad) : Empty := (
    match b {
      MkBad(f) => f(b),
    }
  )

  reject def K (b : Bad) : False := absurd(L(b))
  reject def bad : Bad := MkBad(λ(x : Bad) : Empty => L(x))
  reject def Boom : False := K(bad)
  inductive Pairs := PNil | PCons(hd : Nat × Unit, tl : Pairs)
}

#eval IO.println (run "Positivity" Positivity).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Positivity" Positivity).allAsExpected
#guard (run "Positivity" Positivity).count == 7

/-! The same, with the function type hidden inside a parameter: a field's parameter
arguments must be first-order too. Positive uses of parameters are fine: a list of the
type itself, and a proof field. `Box(A)` and `List(A)` are `Std`'s. -/

ochr PositivityParams uses Std {
  inductive Void : Type

  def unbox (A : Type) (b : Box(A)) : A := (
    match b {
      MkBox(x) => x,
    }
  )

  def absurdV (v : Void) : False := match v {}
  reject inductive Bad := MkBad(f : Box(Π(x : Bad). Void))

  reject def L (b : Bad) : Void := (
    match b {
      MkBad(f) => match f {
        MkBox(g) => g(b),
      },
    }
  )

  reject def K (b : Bad) : False := absurdV(L(b))
  reject def bad : Bad := MkBad(MkBox(λ(x : Bad) : Void => L(x)))
  reject def Boom : False := K(bad)
  reject inductive Neg (A : Type) := MkNeg(f : Π(x : A). Nat)
  inductive Rose (A : Type) := Node(v : A, kids : List(Rose(A)))
  inductive Sig (P : Prop) := MkSig(n : Nat, h : P)

  def SigProof (P : Prop) (s : Sig(P)) : P := (
    match s {
      MkSig(n, h) => h,
    }
  )

  def SigAt : Eq Nat 1 1 := SigProof(Eq Nat 1 1, MkSig(3, refl))

  -- Universes are not cumulative: a proposition is not a `Type` parameter.
  reject def PropBox : Type := Box(Eq Nat 0 1)
}

#eval IO.println (run "PositivityParams" PositivityParams).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "PositivityParams" PositivityParams).allAsExpected
#guard (run "PositivityParams" PositivityParams).count == 14

/-! The paper's version (appendix note 4), with `False` directly. -/

ochr PositivityPaper {
  reject inductive Bad := MkBad(f : Π(x : Bad). False)

  reject def L (b : Bad) : False := (
    match b {
      MkBad(f) => f(b),
    }
  )

  reject def Bad4 : False := L(MkBad(λ(x : Bad) : False => L(x)))
}

#eval IO.println (run "PositivityPaper" PositivityPaper).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "PositivityPaper" PositivityPaper).allAsExpected
#guard (run "PositivityPaper" PositivityPaper).count == 3
